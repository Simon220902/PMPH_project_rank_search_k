let mkFlagArray [m] 't
                (aoa_shp : [m]i32) (zero : t)
                (aoa_val : [m]t) : []t =
    let shp_rot = map (\ i -> if i==0 then 0
                          else aoa_shp[i-1]
                      ) (iota m)
    let shp_scan = scan (+) 0 shp_rot
    let aoa_len = if m == 0 then 0
                  else shp_scan[m-1] + aoa_shp[m-1]
    let shp_ind = map2 (\ size ind ->
                            if size==0 then -1
                            else (i64.i32 ind)
                       ) aoa_shp shp_scan
    in scatter (replicate (i64.i32 aoa_len) zero) shp_ind aoa_val

let scanex [n] 't (op: t -> t -> t) (ne: t) (arr: [n]t) : [n]t =
    scan op ne (map (\ i -> if i == 0 then ne else arr[i-1]) (iota n))

let sgmScanInc [n] 't (op: t -> t -> t) (ne: t)
                      (flags: [n]bool) (arr: [n]t) : [n]t =
    let (_, res) = unzip <|
        scan (\(x_flag,x) (y_flag,y) -> -- extended binop is denoted ⊙
            let fl = x_flag || y_flag
            let vl = if y_flag then y else op x y in (fl, vl)
         ) (false , ne) (zip flags arr)
    in res

let expand [m] 't (plus : t -> t -> t) (t_zero : t)
                  (shp : [m]i32) (vals : [m]t) : []t =
    let (flag_size, flag_val) = zip shp vals |> mkFlagArray shp (0i32,t_zero) |> unzip
    in sgmScanInc (plus) t_zero (map (!= 0i32) flag_size) flag_val

let expandi32 = expand (+) 0i32
let expandi64 = expand (+) 0i64
let expandf32 = expand (+) 0f32
let expandbool = expand (||) false


let partition2 [n] 't                               -- Assume t=i32,n=6
        (p : (t -> bool))                           -- p (x:i32) = 0 == (x%2),
        (arr : [n]t) : ([n]t, i64) =                -- arr = [5,4,2,3,7,8]
    let cs = map p arr                              -- cs  = [F,T,T,F,F,T]
    let tfs = map(\ f -> if f then 1
                              else 0) cs            -- tfs = [0,1,1,0,0,1]
    let isT = scan (+) 0 tfs                        -- isT = [0,1,2,2,2,3]
    let i = isT[n-1]                                -- i   = 3
    
    let ffs = map (\ f -> if f then 0
                               else 1) cs
    let isF = map (+i) <| scan (+) 0 ffs
    let inds = map3 (\c iT iF ->
                        if c then iT-1
                             else iF-1 ) cs isT isF
    let r = scatter (copy arr) inds arr
    in (r, i)

let partition3old [n] 't
        (p1 : (t -> bool))
        (p2 : (t -> bool))
        (arr : [n]t) : ([n]t, (i64, i64)) = 

    -- Partitioning based on p2.
    let cs2 = map p2 arr
    let tfs2 = map (\ f -> if f then 1 else 0 ) cs2
    let isT2 = scan (+) 0 tfs2
    let i2 = isT2[n-1]
    let ffs2 = map (\ f -> if f then 0 else 1 ) cs2
    let isF2 = map (+i2) <| scan (+) 0 ffs2
    let inds2 = map3 (\ c iT iF ->
                        if c then iT-1
                        else iF - 1
                     ) cs2 isT2 isF2
    let arr' = scatter (copy arr) inds2 arr
    
    -- Partitioning based on p1.
    let cs1 = map p1 arr'
    let tfs1 = map (\ f -> if f then 1 else 0 ) cs1
    let isT1 = scan (+) 0 tfs1
    let i1 = isT1[n-1]
    let ffs1 = map (\ f -> if f then 0 else 1 ) cs1
    let isF1 = map (+i1) <| scan (+) 0 ffs1
    let inds1 = map3 (\ c iT iF ->
                        if c then iT-1
                        else iF - 1
                     ) cs1 isT1 isF1
    let arr'' = scatter (copy arr') inds1 arr'
    in
    (arr'', (i1, i2))

let partition3 [n] 't
        (p1 : (t -> bool))
        (p2 : (t -> bool))
        (arr : [n]t) : ([n]t, (i64, i64)) = 
    -- p1
    let cs1 = map p1 arr
    let tfs1 = map (\ f -> if f then 1 else 0 ) cs1
    let isT1 = scan (+) 0 tfs1
    let i1 = isT1[n-1]
    -- p2
    let cs2 = map p2 arr
    let tfs2 = map (\ f -> if f then 1 else 0 ) cs2
    let isT2 = map (+i1) <| scan (+) 0 tfs2
    let i2 = isT2[n-1] - i1
    let ffs = map2 (\ c1 c2 -> if c1 || c2  then 0 else 1) cs1 cs2
    let isF = map (+(i1+i2)) <| scan (+) 0 ffs
    -- Collecting the indices
    let inds = map5 (\ c1 c2 iT1 iT2 iF ->
                        if c1 then iT1-1
                        else if c2 then iT2-1
                        else iF - 1
                     ) cs1 cs2 isT1 isT2 isF

    let arr' = scatter (copy arr) inds arr
    in
    (arr', (i1, i2))

let testnewpartition =
    let arr = [9, 3, 4, 5,2,1,3,57,5,25,2,4]
    let p = arr[(length arr) - 1]
    in (partition3 (< p) (== p) arr) == (partition3old (< p) (== p) arr)




-- Compiler like flattening
-- ==
-- entry: batchNestedRankSearch
-- input {[4i64] [12i32] [1f32, 2f32, 3f32, 4f32, 5f32, 6f32, 7f32, 8f32, 9f32, 10f32, 11f32, 12f32]}
-- output { [4f32] }
entry batchNestedRankSearch [m] [n] (ks: [m]i64) (shp : [m]i32) (As : [n]f32) : [m]f32 =
    let offsets = (map (\ j -> if j == 0 then 0 else shp[j-1]) (iota m)) |> scan (+) 0
    let ps = map2 (\row_offset i -> As[row_offset+i]) offsets (map (\ size -> size - 1i32) shp) 
    let runnings = replicate m true
    let (_, ps, _, _, _) =
        loop (ks : [m]i64, ps : [m]f32, shp : [m]i32, As : []f32, runnings : [m]bool) = (ks, ps, shp, As, runnings)
        while (reduce (||) false runnings) do
            let n' = reduce (+) 0 shp |> i64.i32
            -- PARTITION3 BEGIN FLATTENED
            let (As_partioned, (cnts_lth, cnts_eq)) =
                let As = As :> [n']f32
                -- p1
                let ps_expanded = (expandf32 shp ps) :> [n']f32
                    -- let (flag_size, flag_p) = zip shp ps |> mkFlagArray shp (0,0) |> unzip
                    -- in sgmScanInc (+) 0 flag_size flag_p
                let cs1s = map2 (<) As ps_expanded
                let tfs1s = (map (\ f -> if f then 1 else 0 ) cs1s) 
                let As_flags = (mkFlagArray shp 0 (replicate m 1) |> map (== 1)) :> [n']bool
                let isT1s = sgmScanInc (+) 0 As_flags tfs1s
                let offsets = (map (\ j -> if j == 0 then 0 else shp[j-1]) (iota m)) |> scan (+) 0
                let i1s = map2 (\row_offset i -> isT1s[row_offset+i]) offsets (map (\size -> size-1i32) shp) 
                -- p2
                let cs2s = map2 (==) As ps_expanded
                let tfs2s = map (\ f -> if f then 1 else 0 ) cs2s
                let isT2s_s1 = sgmScanInc (+) 0i32 As_flags tfs2s
                let i1s_expanded = expandi32 shp i1s :> [n']i32
                    -- let (flag_size, flag_i1) = zip shp i1s |> mkFlagArray shp (0,0) |> unzip
                    -- in sgmScanInc (+) 0 flag_size flag_i1
                let isT2s = map2 (\ i1 iT2_s1 -> iT2_s1 + i1) i1s_expanded isT2s_s1
                let offsets = (map (\ j -> if j == 0 then 0 else shp[j-1]) (iota m)) |> scan (+) 0
                let i2s_s1 = map2 (\ offset i -> isT2s[offset+i]) offsets (map (\size -> size-1i32) shp)
                let i2s = map2 (\ i2_s1 i1 -> i2_s1 - i1) i2s_s1 i1s
                let ffss = map2 (\ c1 c2 -> if c1 || c2 then 0 else 1) cs1s cs2s
                let isFs_s1 = sgmScanInc (+) 0 As_flags ffss
                let i2s_expanded = expandi32 shp i2s :> [n']i32
                    -- let (flag_size, flag_i2) = zip shp i2s |> mkFlagArray shp (0,0) |> unzip
                    -- in sgmScanInc (+) 0 flag_size flag_i2
                let isFs = map3 (\ i1 i2 isF_s1 -> i1 + i2 + isF_s1) i1s_expanded i2s_expanded isFs_s1
                let indss = map5 (\ c1 c2 iT1 iT2 iF ->
                                        if c1 then iT1-1
                                        else if c2 then iT2-1
                                        else iF - 1
                                ) cs1s cs2s isT1s isT2s isFs
                            :> [n']i32
                let offsets = map (\ i -> if i == 0 then 0 else shp[i-1]) (iota m) |> scan (+) 0
                let offsets_expanded =
                    let (flag_size, flag_offset) = zip shp offsets |> mkFlagArray shp (0,0) |> unzip
                    in sgmScanInc (+) 0 (map (!= 0) flag_size) flag_offset :> [n']i32
                let indss' = map2 (+) offsets_expanded indss
                let arrs' = scatter (copy As) (map i64.i32 indss') As
                in (arrs', (i1s, i2s))
            -- PARTITION3 END
            let cnts_lth = map i64.i32 cnts_lth :> [m]i64
            let cnts_eq = map i64.i32 cnts_eq :> [m]i64
            let ks = ks :> [m]i64
            let cnts_gth = map3 (\ size cnt_lth cnt_eq -> size - cnt_lth - cnt_eq) (map i64.i32 shp) cnts_lth cnts_eq
            -- We separate the calculation of ks', ps', runnings' and As'
            let ks' = map4 (\ k cnt_lth cnt_eq running ->
                            if k <= cnt_lth && running then k
                            else if k <= cnt_lth + cnt_eq || not running then k
                            else k-cnt_lth-cnt_eq
                          ) ks cnts_lth cnts_eq runnings
            let ps' =
                    let row_offsets = scanex (+) 0 shp |> map i64.i32
                    let row_offsets = row_offsets :> [m]i64
                    in
                    map5 (\ k p (cnt_lth, cnt_eq, cnt_gth) running row_offset -> 
                                if k <= cnt_lth && running
                                then As_partioned[row_offset+cnt_lth-1]
                                else if k <= cnt_lth + cnt_eq || not running
                                then p
                                else As_partioned[row_offset+cnt_lth+cnt_eq+cnt_gth-1]
                           ) ks ps (zip3 cnts_lth cnts_eq cnts_gth) runnings row_offsets
    
            let runnings' =  map4 (\ k cnt_lth cnt_eq running -> 
                                    if k <= cnt_lth && running
                                    then true
                                    else if k <= cnt_lth + cnt_eq || not running
                                    then false
                                    else true
                                  ) ks cnts_lth cnts_eq runnings

            -- We also need to calculate the new shape.
            let shp' = map5 (\ k cnt_lth cnt_eq cnt_gth running -> 
                                if k <= cnt_lth && running
                                then cnt_lth
                                else if k <= cnt_lth + cnt_eq || not running
                                then 0
                                else cnt_gth
                            ) ks cnts_lth cnts_eq cnts_gth runnings
            
            let As' =
                let n' = (reduce (+) 0 shp')
                let shp'_i64 = (map i32.i64 shp')
                let old_offset_expanded = (expandi64 shp'_i64 (scanex (+) 0 (map i64.i32 shp)))
                let old_offset_expanded = old_offset_expanded :> [n']i64
                let new_offset_expanded = expandi64 shp'_i64 (scanex (+) 0 shp') :> [n']i64
                let newis =  iota n'
                let ks_expanded = expandi64 shp'_i64 ks :> [n']i64
                let runnings_expanded = expandbool shp'_i64 runnings :> [n']bool
                let cnt_lth_expanded = expandi64 shp'_i64 cnts_lth :> [n']i64
                let cnt_eq_expanded = expandi64 shp'_i64 cnts_eq :> [n']i64
                in
                map4 (\ newi old_offset new_offset (k, running, cnt_lth, cnt_eq) ->
                            let i = newi - new_offset in
                            if k <= cnt_lth && running
                            then
                                let oldi = old_offset + i
                                in As_partioned[oldi]
                            else 
                                let oldi = old_offset + i + cnt_lth + cnt_eq
                                in As_partioned[oldi]
                    ) newis old_offset_expanded new_offset_expanded (zip4 ks_expanded runnings_expanded cnt_lth_expanded cnt_eq_expanded)

            in (ks', ps', (map i32.i64 shp'), As', runnings')
    in ps

