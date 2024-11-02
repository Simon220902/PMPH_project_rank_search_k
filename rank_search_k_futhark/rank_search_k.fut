import "lib/github.com/diku-dk/sorts/radix_sort"

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
    let i = if n > 0 then isT[n-1] else 0           -- i   = 3
    
    let ffs = map (\ f -> if f then 0
                               else 1) cs
    let isF = map (+i) <| scan (+) 0 ffs
    let inds = map3 (\c iT iF ->
                        if c then iT-1
                             else iF-1 ) cs isT isF
    let r = scatter (copy arr) inds arr
    in (r, i)

let partition3 [n] 't
        (p1 : (t -> bool))
        (p2 : (t -> bool))
        (arr : [n]t) : ([n]t, (i64, i64)) = 
    -- p1
    let cs1 = map p1 arr
    let tfs1 = map (\ f -> if f then 1 else 0 ) cs1
    let isT1 = scan (+) 0 tfs1
    let i1 = if n>0 then isT1[n-1] else 0
    -- p2
    let cs2 = map p2 arr
    let tfs2 = map (\ f -> if f then 1 else 0 ) cs2
    let isT2 = map (+i1) <| scan (+) 0 tfs2
    let i2 = if n>0 then isT2[n-1] - i1 else 0
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


module Partition3 = {
    let batch [m] [n] (p1: (f32->f32->bool)) (p2 : (f32->f32->bool))
                            (As : [n]f32) (shp : [m]i32) (arg2s : [m]f32) =
        let arg2s_expanded = expandf32 shp arg2s :> [n]f32
        let cs1s = map2 p1 As arg2s_expanded :> [n]bool
        let tfs1s = map (\ f -> if f then 1 else 0 ) cs1s :> [n]i32
        let As_flags = mkFlagArray shp false (replicate m true) :> [n]bool
        let isT1s = sgmScanInc (+) 0 As_flags tfs1s
        let offsets = scanex (+) 0 shp :> [m]i32
        let i1s = map2 (\offset i ->
                            if i == -1 then 0
                            else            isT1s[offset+i]
                        ) offsets (map (\size -> size - 1) shp)
        let cs2s = map2 p2 As arg2s_expanded
        let tfs2s = map (\ f -> if f then 1 else 0 ) cs2s
        let isT2s =
            let tfs2s_scan = sgmScanInc (+) 0 As_flags tfs2s :> [n]i32
            let i1s_expanded = expandi32 shp i1s :> [n]i32
            in map2 (+) i1s_expanded tfs2s_scan
        let i2s = map2 (\offset i ->
                            if i == -1 then 0
                            else            isT2s[offset+i]
                        ) offsets (map (\size -> size - 1) shp)
                |> map2 (\ i1 i2 -> i2 - i1) i1s
        let ffss = map2 (\ c1 c2 -> if c1 || c2  then 0 else 1) cs1s cs2s
        let isFs =
            let ffss_scan = sgmScanInc (+) 0 As_flags ffss :> [n]i32
            let i1plusi2 = map2 (+) i1s i2s :> [m]i32
            let i1plusi2s_expanded = expandi32 shp i1plusi2 :> [n]i32
            in map2 (+) i1plusi2s_expanded ffss_scan
    
        let indss =
            let offsets_expanded = expandi32 shp offsets :> [n]i32
            in (map5 (\ c1 c2 iT1 iT2 iF ->
                        if c1 then iT1-1
                        else if c2 then iT2-1
                        else iF - 1
                    ) cs1s cs2s isT1s isT2s isFs)
                |> map2 (+) offsets_expanded
    
        let As' = scatter (copy As) (map i64.i32 indss) As
        in
        (As', (i1s, i2s))
}

module RankSearchK = {
    let radixSortRankSearchBatch [m] [n] (ks: [m]i32) (shp: [m]i32) (A: [n]f32) : [m]f32 =
        let radix_sort_based_rank_search_k (k: i32) (A: []f32) : f32 =
            let sorted_array = radix_sort f32.num_bits f32.get_bit A in
            sorted_array[k-1]
        let shp = map i64.i32 shp
        let start_indices = map (\ elem -> elem - shp[0]) (scan (+) 0 shp)
        in map3 (\ k size i0 ->
                    let a = map (\ i -> A[i+i0]) (iota size) in -- A[i0:(i0+size)] in -- We don't know whether a slize or a map-iota are better?
                    radix_sort_based_rank_search_k k a
                ) ks shp start_indices
    let generalizedHumanReasoningBatchRankSearchOptimized [m] [n] 't (lth : t -> t -> bool) (eq : t -> t -> bool) (zero : t)
                                                           (ps : [m]t) (ks: [m]i32) (shp: [m]i32)
                                                           (II1: *[n]i32) (A: [n]t) : [m]t =
        let result = replicate m zero
        
        let (_,_,_,_,_,result) =
            loop (ks: [m]i32, ps : [m]t, shp: [m]i32, II1 : []i32, A : []t, result) = (ks, ps, shp, II1, A, result)
            while (length A > 0) do
                let ps_expanded = map (\i -> ps[i]) II1
                let lth_eq_per_elem = map2 (\ elem p -> (if lth elem p then (true,false) else if eq elem p then (false,true) else (false,false))) A ps_expanded
                let (cnt_lth, cnt_eq) =
                    map (\ (a, b) -> (i32.bool a, i32.bool b)) lth_eq_per_elem
                    |> reduce_by_index (replicate m (0, 0)) (\ (a, b) (c, d) -> (a+c, b+d)) (0, 0) (map i64.i32 II1)
                    |> unzip
                let kinds = map3 (\ k lth eq->
                                    if k == -1            then -1i8
                                    else if k <= lth      then 0i8
                                    else if k <= (lth+eq) then 1i8
                                    else                       2i8
                                ) ks cnt_lth cnt_eq
                let (shp', ks') = map5 (\ len k kind lth eq->
                                            if      kind == -1i8 then (len, -1)
                                            else if kind ==  0i8 then (lth, k)
                                            else if kind ==  1i8 then (0, -1)
                                            else (len - (lth + eq), k - (lth + eq))
                                        ) shp ks kinds cnt_lth cnt_eq
                                |> unzip
                
                let (_, is, vs) = filter (\(kind, _, _) -> kind == 1i8) (zip3 kinds (iota m) ps) |> unzip3
                let result' = scatter result is vs
                
                let (_, A', II1') = zip3 lth_eq_per_elem A II1
                                |> filter (\ ((lth, eq), _, i) ->
                                            let kind = kinds[i] in
                                            if kind == -1 || kind == 1 then false
                                            else if kind == 0 then lth
                                            else (not lth) && (not eq)
                                    )
                                |> unzip3

                let ps' = map2 (\ i size -> if size > 0 then A'[i-1] else zero) (scan (+) 0 shp') shp'
                in (ks', ps', shp', II1', A', result')
        in result


    let humanReasoningBatchRankSearchOptimized [m] [n] (ps : [m]f32) (ks: [m]i32) (shp: [m]i32)
                                            (II1: *[n]i32) (A: [n]f32) : [m]f32 =
        generalizedHumanReasoningBatchRankSearchOptimized (<) (==) (0f32) ps ks shp II1 A

    let humanReasoningBatchRankSearch [n] [m] (ks: [m]i32) (As: [n]f32)
                                (shp : [m]i32) (II1 : [n]i64) : [m]f32 =
        let (_, _, _, _, results) =
            loop ((ks : [m]i32) , As, (shp : [m]i32), II1, results : [m]f32) = (ks, As, shp, II1, (replicate m f32.nan))
            while (length As > 0) do
                let ps  = map3 (\ i size result ->
                                    if size > 0 then As[i-1]
                                    else             result
                                ) (scan (+) 0 shp) shp results
                let ps_expanded = map (\i -> ps[i]) II1
                let lth_per_elem = map2 (\ elem p -> i32.bool (elem < p)) As ps_expanded
                let eq_per_elem = map2 (\ elem p -> i32.bool (elem == p)) As ps_expanded
                let cnts_lth = reduce_by_index (replicate m 0) (+) 0 II1 lth_per_elem :> [m]i32
                let cnts_eq = reduce_by_index (replicate m 0) (+) 0 II1 eq_per_elem :> [m]i32
                let kinds = map3 (\ k cnt_lth cnt_eq ->
                                    if k == -1                    then -1
                                    else if k <= cnt_lth          then 0
                                    else if k <= cnt_lth + cnt_eq then 1
                                    else                               2
                                ) ks cnts_lth cnts_eq
                let ks' = map4 (\ kind k cnt_lth cnt_eq ->
                                if kind == -1     then -1i32
                                else if kind == 0 then k
                                else if kind == 1 then -1i32
                                else                   k - cnt_lth - cnt_eq
                               ) kinds ks cnts_lth cnts_eq
                let results' = map3 (\ kind p result ->
                                        if kind == 1 then p
                                        else              result
                                    ) kinds ps results
                let shp' = map4 (\ kind cnt_lth cnt_eq size ->
                                    if kind == -1     then 0
                                    else if kind == 0 then cnt_lth
                                    else if kind == 1 then 0
                                    else                   size - cnt_lth - cnt_eq
                                ) kinds cnts_lth cnts_eq shp
                let (_, _, As', II1') = filter (\ (lth, eq, _, i) ->
                                                    let kind = kinds[i] in
                                                    if kind == -1     then false
                                                    else if kind == 0 then lth == 1
                                                    else if kind == 1 then false
                                                    else                   lth == 0 && eq == 0
                                            ) (zip4 lth_per_elem eq_per_elem As II1)
                                    |> unzip4
                in (ks', As', shp', II1', results')
        in results

    let compilerThinkingBatchRankSearch [m] [n] (ks: [m]i32) (As: [n]f32) (shp : [m]i32) : [m]f32 =
        let (_, _, _, result) =
            loop (ks, As, shp, results) = (ks, As, shp, (replicate m f32.nan))
            while (reduce (+) 0 shp) > 0 do
                let ps =
                    let offsets = scanex (+) 0 shp
                    in map3 (\ offset i result ->
                                if i>=0 then As[offset+i]
                                else         result
                            ) offsets (map (\ size -> size-1) shp) results
                let (As_partioned, (cnts_lth, cnts_eq)) = Partition3.batch (<) (==) As shp ps
                let ks' = map4 (\ k cnt_lth cnt_eq size ->
                                    if k <= cnt_lth && size > 0
                                    then k
                                    else if k <= cnt_lth + cnt_eq || size == 0
                                    then k
                                    else k-cnt_lth-cnt_eq
                                ) ks cnts_lth cnts_eq shp
                let results' =  map5 (\ k (cnt_lth, cnt_eq) size p result -> 
                                        if k <= cnt_lth && size > 0
                                        then result
                                        else if k <= cnt_lth + cnt_eq || size == 0
                                        then p
                                        else result
                                    ) ks (zip cnts_lth cnts_eq) shp ps results
                let shp' = map4 (\ k cnt_lth cnt_eq size -> 
                                    if k <= cnt_lth && size > 0
                                    then cnt_lth
                                    else if k <= cnt_lth + cnt_eq || size == 0
                                    then 0
                                    else size - cnt_lth - cnt_eq
                                ) ks cnts_lth cnts_eq shp
                let As' =
                    let n' = reduce (+) 0 shp' |> i64.i32
                    let old_offsets_expanded =
                        scanex (+) 0 shp
                        |> expandi32 shp'
                        |> map i64.i32 :> [n']i64
                    let new_offsets_expanded =
                        scanex (+) 0 shp'
                        |> expandi32 shp'
                        |> map i64.i32 :> [n']i64
                    let ks_expanded = expandi32 shp' ks |> map i64.i32 :> [n']i64
                    let cnts_lth_expanded = expandi32 shp' cnts_lth |> map i64.i32 :> [n']i64
                    let cnts_eq_expanded = expandi32 shp' cnts_eq |> map i64.i32 :> [n']i64
                    in map4 (\ newi old_offset new_offset (k, cnt_lth, cnt_eq) ->
                                let i = newi - new_offset in
                                if k <= cnt_lth
                                then
                                    let oldi = old_offset + i
                                    in As_partioned[oldi]
                                else
                                    let oldi = old_offset + i + cnt_lth + cnt_eq
                                    in As_partioned[oldi]
                            ) (iota n') old_offsets_expanded new_offsets_expanded
                            (zip3 ks_expanded cnts_lth_expanded cnts_eq_expanded)
                in (ks', As', shp', results')
        in result

}