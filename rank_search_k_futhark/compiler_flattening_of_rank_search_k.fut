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

    let arr' = scatter (copy arr) inds arr -- map (scatter) FLATTEN THIS
    in
    (arr', (i1, i2))


-- let rankSearch (k: i64) (A: []f32) : f32 =
--     let p = random_element A
--     let p = (length A) - 1
--     let A_lth_p = filter (< p) A
--     let A_eq_p = filter (==p) A
--     let A_gth_p = filter (> p) A
--     if (k <= A_lth_p.length)
--         then rankSearch k A_lth_p
--     else if (k <= A_lth_p.length + A_eq_p.length)
--         then p
--     else rankSearch (k - A_lth_p.length - A_eq_p.length) A_gth_p
-- let main [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 = map2 rankSearch ks As

-- What type of nested parallelism do we have here?
-- map2 (loop (3xfilter))
-- Flattening:
-- Swapping parallel map2 ("loop") inside:
-- -- loop ( map2 (3xfilter)) (BATCHED)

entry nestedLoopRankSearch (k: i64) (A: []f32) : f32 =
    let p = A[(length A) - 1]
    let running = true in
    let (_, p, _, _) =
        loop (k, p, A, running) = (k, p, A, running)
        while running do
            let A_lth_p = filter (<  p) A
            let A_eq_p = filter (== p) A
            let A_gth_p = filter (>  p) A in
            if (k <= (length A_lth_p))
            then (k, A_lth_p[(length A_lth_p) -1], A_lth_p, true)
            else if (k <= (length A_lth_p) + (length A_eq_p))
            then (k, p, A, false)
            else ((k - (length A_lth_p) - (length A_eq_p)), A_gth_p[(length A_gth_p)-1], A_gth_p, true)
    in p

let main [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 = map2 rankSearch ks As

-- Now we want to switch the loop and map2.
-- This means that we do one iteration for each of the arrays. The condition now is whether there is a running variable that is true (i.e. reduce (or) false array_of_running).
-- Since the outer loop is now doing it for all the different arrays in the batch we need to expand the tuple being updated in the while loop.
-- 
let oneStepRankSearch (k: i64, p:f32, A: []f32, running : bool) : (i64, f32, []f32, bool) =
    let A_lth_p = filter (<  p) A
    let A_eq_p = filter (== p) A
    let A_gth_p = filter (>  p) A in
    if (k <= (length A_lth_p)) and running
    then (k, A_lth_p[(length A_lth_p) -1], A_lth_p, true)
    else if (k <= (length A_lth_p) + (length A_eq_p)) or not running
    then (k, p, A, false)
    else ((k - (length A_lth_p) - (length A_eq_p)), A_gth_p[(length A_gth_p)-1], A_gth_p, true)

let batchNestedRankSearch [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 =
    let ps = map (\ A -> A[(length A)-1]) As
    let runnings = replicate true m

    let (_, ps, _, _) =
        loop (ks, ps, As, runnings) = (ks, ps, As, runnings)
        while (reduce (or) false runnings) do
            zip4 ks ps As runnings
            |> map oneStepRankSearch
            |> unzip4
    in ps

-- Now we can distribute the map over the oneStepRankSearch.
let batchNestedRankSearch [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 =
    let ps = map (\ A -> A[(length A)-1]) As
    let runnings = replicate true m

    let (_, ps, _, _) =
        loop (ks, ps, As, runnings) = (ks, ps, As, runnings)
        while (reduce (or) false runnings) do
            let A_lth_ps = map2 (\ A p -> filter (<  p) A) As ps
            let A_eq_ps = map2 (\ A p -> filter (== p) A) As ps
            let A_gth_ps = map2 (\ A p -> filter (> p) A) As ps
            in
            map (\ k p As A_lth_p A_eq_p A_gth_p running -> -- THIS IS ONLY PSEUDOCODE :D
                    if (k <= (length A_lth_p)) and running
                    then (k, A_lth_p[(length A_lth_p) -1], A_lth_p, true)
                    else if (k <= (length A_lth_p) + (length A_eq_p)) or not running
                    then (k, p, [], false)
                    else ((k - (length A_lth_p) - (length A_eq_p)), A_gth_p[(length A_gth_p)-1], A_gth_p, true)
                ) ks ps As A_lth_ps A_eq_ps A_gth_ps runnings |> unzip
    in ps

-- Before we can flatten this we need to replace the map (filter) s with something that does not contain a filter.
-- Which we can do with partition3.
let batchNestedRankSearch [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 =
    let ps = map (\ A -> A[(length A)-1]) As
    let runnings = replicate true m
    let (_, ps, _, _) =
        loop (ks, ps, As, runnings) = (ks, ps, As, runnings)
        while (reduce (or) false runnings) do
            let (As_partioned, cnts_lth_eq) = map2 (\ A p ->
                                                        partition3 (< p) (== p) A
                                                    ) As ps
                                                    |> unzip
            let (cnts_lth, cnts_eq) = unzip cnts_lth_eq
            let cnts_gth = map3 (\ A_partioned cnt_lth cnt_eq -> (length A_partioned) - cnt_lth - cnt_eq) As_partioned cnts_lth cnts_eq

            in
            let (ks', ps', As', runnings') =
                map (\ k p A_partioned cnt_lth cnt_eq cnt_gth running -> 
                        if k <= cnt_lth && running
                        then
                            let is = iota cnt_lth
                            let A_lth = map (\ i -> A_partioned[i]) is
                            in (k, A_lth[cnt_lth-1], A_lth, true)
                        else if k <= cnt_lth + cnt_eq || not running
                        then (k, p, [], false)
                        else
                            let is = map (\ i -> cnt_lth + cnt_eq + i ) (iota cnt_gth)
                            let A_gth = filter (> p) A_partioned
                            in ((k-cnt_lth-cnt_eq), A_gth[cnt_gth-1], A_gth, true)
                    ) ks ps As_partioned cnts_lth cnts_eq cnts_gth runnings
                    |> unzip4
            in (ks', ps', As', runnings')
    in ps
-- Now we can make loop distribution on partition3
let batchNestedRankSearch [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 =
    let ps = map (\ A -> A[(length A)-1]) As
    let runnings = replicate true m
    let (_, ps, _, _) =
        loop (ks, ps, As, runnings) = (ks, ps, As, runnings)
        while (reduce (or) false runnings) do
            -- PARTITION3 BEGIN
            -- let (As_partioned, cnts_lth_eq) = map2 (\ A p ->
            --                                             partition3 (< p) (== p) A
            --                                         ) As ps
            --                                         |> unzip
            -- let (cnts_lth, cnts_eq) = unzip cnts_lth_eq
            
            -- p1
            let cs1s = map2 (\ p arr -> map (< p) arr) p As
            let tfs1s = map (\ cs1 -> map (\ f -> if f then 1 else 0 ) cs1) cs1s
            let isT1s = map (scan (+) 0) tfs1s
            let i1s = map (\ isT1 -> isT1[(length isT1) - 1]) isT1s
            -- p2
            let cs2s = map2 (\ p arr -> map (== p) arr) p As
            let tfs2s = map (\ cs2 -> map (\ f -> if f then 1 else 0 ) cs2) cs2s
            let isT2s = map2 (\ i1 tfs2 -> map (+i1) <| scan (+) 0 tfs2) i1s tfs2s
            let i2s = map2 (\ isT2 i1 -> isT2[(length isT2)-1] - i1) isT2s i1s
            let ffss = map2 (map2 (\ c1 c2 -> if c1 || c2  then 0 else 1)) cs1s cs2s
            let isFs = map3 (\ i1 i2 ffs -> map (+(i1+i2)) <| scan (+) 0 ffs) i1s i2s ffss
            -- Collecting the indices
            let indss = map5 ( map5 (\ c1 c2 iT1 iT2 iF ->
                                    if c1 then iT1-1
                                    else if c2 then iT2-1
                                    else iF - 1
                                )) cs1s cs2s isT1s isT2s isFs

            let arrs' = map2 (\ arr inds -> scatter (copy arr) inds arr) As indss
            let (As_partioned, (cnts_lth, cnts_eq)) = (arrs', (i1s, i2s))
            -- PARTITION3 END
            let cnts_gth = map3 (\ A_partioned cnt_lth cnt_eq -> (length A_partioned) - cnt_lth - cnt_eq) As_partioned cnts_lth cnts_eq

            in
            let (ks', ps', As', runnings') =
                map (\ k p A_partioned cnt_lth cnt_eq cnt_gth running -> 
                        if k <= cnt_lth && running
                        then
                            let is = iota cnt_lth
                            let A_lth = map (\ i -> A_partioned[i]) is
                            in (k, A_lth[cnt_lth-1], A_lth, true)
                        else if k <= cnt_lth + cnt_eq || not running
                        then (k, p, [], false)
                        else
                            let is = map (\ i -> cnt_lth + cnt_eq + i ) (iota cnt_gth)
                            let A_gth = filter (> p) A_partioned
                            in ((k-cnt_lth-cnt_eq), A_gth[cnt_gth-1], A_gth, true)
                    ) ks ps As_partioned cnts_lth cnts_eq cnts_gth runnings
                    |> unzip4
            in (ks', ps', As', runnings')
    in ps

-- Now we flatten. Giving As as a flat array and a shp.
-- We use the following flattening rules: map(index), map (replicate), map (map), map (scan)
-- Exercise 2: Flatten Map (index)
-- F map2 (\row i -> row[i]) mat inds =>
-- let row_offsets = scanex (+) 0 shp
--                 = (map (\ j -> if j == 0 then 0 else shp[j-1]) (iota (length shp))) |> scan (+) 0
-- map2 (\row_offset i -> mat[row_offset+i]) row_offsets inds
-- Our deduction of: Flatten Map (scatter)
-- F map (\ dst is vs -> scatter dst is vs) dsts iss vss =>
-- ** assuming dsts, vss and iss is flattened elsewhere **
-- let offsets = scanex (+) 0 shp
--             = map (\ i -> if i == 0 then 0 else shp[i-1]) (iota (length shp)) |> scan (+) 0
-- let offsets_expanded =
--      let (flag_size, flag_offset) = zip shp offsets |> mkFlagArray shp (0,0) |> unzip
--      in sgmScanInc (+) 0 flag_size flag_offset
-- let iss' = map2 (+) offsets_expanded iss
-- scatter dsts iss' vss

let batchNestedRankSearch [m] [n] (ks: [m]i64) (shp : [m]i32) (As : [n] f32) : [m]f32 =
    -- let ps = map (\ A -> A[(length A)-1]) As 
    -- let ps = map2 (\ A i -> A[i]) As (map (\ A -> (length A) - 1) As)
    --  (map (\ A -> (length A) - 1) As) ==  (map (-1) shp)
    -- ps now fits on Map (index)
    -- FLAT FROM HERE
    let offsets = (map (\ j -> if j == 0 then 0 else shp[j-1]) (iota (length shp))) |> scan (+) 0
    let ps = map2 (\row_offset i -> As[row_offset+i]) offsets (map (-1) shp) 
    let runnings = replicate true m
    let (_, ps, _, _) =
        loop (ks, ps, shp, As, runnings) = (ks, ps, shp, As, runnings)
        while (reduce (or) false runnings) do
            -- PARTITION3 BEGIN
            -- let (As_partioned, cnts_lth_eq) = map2 (\ A p ->
            --                                             partition3 (< p) (== p) A
            --                                         ) As ps
            --                                         |> unzip
            -- let (cnts_lth, cnts_eq) = unzip cnts_lth_eq
            
            -- p1
            -- let cs1s = map2 (\ p arr -> map (< p) arr) ps As
            -- we pull out the arguments
            -- let ps_expanded = map2 (\ arr p -> replicate (length arr) p) As ps
            -- let cs1s = map2 (map2 (<)) As ps_expanded
            -- Using shp we can write ps_expanded as
            -- let ps_expanded = map2 (\ size p -> replicate size p) shp ps
            -- Now we flatten these:
            let ps_expanded = 
                let (flag_size, flag_p) = zip shp ps |> mkFlagArray shp (0,0) |> unzip
                in sgmScanInc (+) 0 flag_size flag_p
            let cs1s = map2 (<) As ps_expanded
            
            
            -- let tfs1s = map (\ cs1 -> map (\ f -> if f then 1 else 0 ) cs1) cs1s
            let tfs1s = map (\ f -> if f then 1 else 0 ) cs1s
            
            -- let isT1s = map (scan (+) 0) tfs1s
            let As_flags = mkFlagArray shp 0 (replicate m 1)
            let isT1s = sgmScanInc (+) 0 As_flags tfs1s


            -- let i1s = map (\ isT1 -> isT1[(length isT1) - 1]) isT1s
            -- let i1s = map2 (\ isT1 i -> isT1[i]) isT1s (map (\ isT1 -> (length isT1)-1) isT1s)
            -- let i1s = map2 (\ isT1 i -> isT1[i]) isT1s (map (-1) shp)
            let offsets = (map (\ j -> if j == 0 then 0 else shp[j-1]) (iota m)) |> scan (+) 0
            let i1s = map2 (\row_offset i -> isT1s[row_offset+i]) offsets (map (-1) shp) 
            

            -- p2
            -- let cs2s = map2 (\ p arr -> map (== p) arr) p As
            let cs2s = map2 (==) As ps_expanded
            
            
            -- let tfs2s = map (\ cs2 -> map (\ f -> if f then 1 else 0 ) cs2) cs2s
            let tfs2s = map (\ f -> if f then 1 else 0 ) cs2s
            

            -- let isT2s = map2 (\ i1 tfs2 -> map (+i1) <| scan (+) 0 tfs2) i1s tfs2s
            -- let isT2s = map2 (\ i1 tfs2 -> map (+i1) (scan (+) 0 tfs2)) i1s tfs2s
            -- We can split the nested map scan up into two different things.
            -- let isT2s_s1 = map (scan (+) 0) tfs2s
            -- let isT2s = map2 (\ i1 isT2_s1 -> map (+i1) isT2_s1) i1s isT2s_s1
            let isT2s_s1 = sgmScanInc (+) 0 As_flags tfs2s
            let i1s_expanded =
                let (flag_size, flag_i1) = zip shp i1s |> mkFlagArray shp (0,0) |> unzip
                in sgmScanInc (+) 0 flag_size flag_i1
            let isT2s = map2 (\ i1 iT2_s1 -> isT2_s1 + i1) i1s_expanded isT2_s1
            
            
            -- let i2s = map2 (\ isT2 i1 -> isT2[(length isT2)-1] - i1) isT2s i1s
            -- We can split this up into two
            -- let i2s_s1 = map2 (\ isT2 i -> isT2[i]) (map (\ isT2 -> (length isT2) -1) isT2s)
            --            = map2 (\ isT2 i -> isT2[i]) (map (-1) shp)
            -- let i2s = map2 (\ i2_s1 i1 -> i2_s1 - i1) i2s_s1 i1s
            -- Then we can flatten it:
            let offsets = (map (\ j -> if j == 0 then 0 else shp[j-1]) (iota (length shp))) |> scan (+) 0
            let i2s_s1 = map2 (\ offset i -> isT2s[offset+i]) offsets (map (-1) shp)
            let i2s = map2 (\ i2_s1 i1 -> i2_s1 - i1) i2s_s1 i1s

            
            
            -- let ffss = map2 (map2 (\ c1 c2 -> if c1 || c2  then 0 else 1)) cs1s cs2s
            let ffss = map2 (\ c1 c2 -> if c1 || c2 then 0 else 1) cs1s cs2s
            
            
            -- let isFs = map3 (\ i1 i2 ffs -> map (+(i1+i2)) <| scan (+) 0 ffs) i1s i2s ffss
            -- let isFs = map3 (\ i1 i2 ffs -> map (+(i1+i2)) (scan (+) 0 ffs)) i1s i2s ffss
            -- We can once again split it up internally
            -- let isFs_s1 = map (scan (+) 0) ffss
            -- let isFs = map3 (\ i1 i2 isF_s1 -> map (+(i1 + i2)) isF_s1) i1s i2s isFs_s1
            let isFs_s1 = sgmScanInc (+) 0 A_flag ffss
            let i2s_expanded =
                let (flag_size, flag_i2) = zip shp i2s |> mkFlagArray shp (0,0) |> unzip
                in sgmScanInc (+) 0 flag_size flag_i2
            let isFs = map3 (\ i1 i2 isF_s1 -> i1 + i2 + isF_s1) i1s_expanded i2s_expanded isFs_s1

            
            -- Collecting the indices
            -- let indss = map5 ( map5 (\ c1 c2 iT1 iT2 iF ->
            --                         if c1 then iT1-1
            --                         else if c2 then iT2-1
            --                         else iF - 1
            --                     )) cs1s cs2s isT1s isT2s isFs
            let indss = map5 (\ c1 c2 iT1 iT2 iF ->
                                    if c1 then iT1-1
                                    else if c2 then iT2-1
                                    else iF - 1
                             ) cs1s cs2s isT1s isT2s isFs


            -- let arrs' = map2 (\ arr inds -> scatter (copy arr) inds arr) As indss
            -- let arrs' = map3 (\ dst inds arr -> scatter dst inds arr) (copy As) indss As
            let offsets = map (\ i -> if i == 0 then 0 else shp[i-1]) (iota m) |> scan (+) 0
            let offsets_expanded =
                let (flag_size, flag_offset) = zip shp offsets |> mkFlagArray shp (0,0) |> unzip
                in sgmScanInc (+) 0 flag_size flag_offset
            let indss' = map2 (+) offsets_expanded indss
            let arss' = scatter (copy As) indss' As

            let (As_partioned, (cnts_lth, cnts_eq)) = (arrs', (i1s, i2s))
            -- PARTITION3 END
            
            
            -- let cnts_gth = map3 (\ A_partioned cnt_lth cnt_eq -> (length A_partioned) - cnt_lth - cnt_eq) As_partioned cnts_lth cnts_eq
            -- let cnts_gth = map3 (\ size cnt_lth cnt_eq -> size - cnt_lth - cnt_eq) shp cnts_lth cnts_eq
            let cnts_gth = map3 (\ size cnt_lth cnt_eq -> size - cnt_lth - cnt_eq) shp cnts_lth cnts_eq
            -- NOT FLAT FROM HERE
            in
            -- let (ks', ps', As', runnings') =
            --     map (\ k p A_partioned cnt_lth cnt_eq cnt_gth -> 
            --             if k <= cnt_lth && running
            --             then
            --                 let is = iota cnt_lth
            --                 let A_lth = map (\ i -> A_partioned[i]) is
            --                 in (k, A_lth[cnt_lth-1], A_lth, true)
            --             else if k <= cnt_lth + cnt_eq || not running
            --             then (k, p, [], false)
            --             else
            --                 let is = map (\ i -> cnt_lth + cnt_eq + i) (iota cnt_gth)
            --                 in ((k-cnt_lth-cnt_eq), A_gth[cnt_gth-1], A_gth, true)
            --         ) ks ps As_partioned cnts_lth cnts_eq cnts_gth
            --         |> unzip4
            -- We separate the calculation of ks', ps', runnings' and As'
            let ks' = map4 (\ k cnt_lth cnt_eq running ->
                            if k <= cnt_lth && running then k
                            else if k <= cnt_lth + cnt_eq || not running then k
                            else k-cnt_lth-cnt_eq
                          ) ks cnts_lth cnts_eq runnings
            let ps' = map5 (\ p A_partioned cnt_lth cnt_eq running -> 
                                if k <= cnt_lth && running
                                then A_partioned[cnt_lth-1]
                                else if k <= cnt_lth + cnt_eq || not running
                                then p
                                else A_partioned[(length A_partioned) - 1]
                           ) ps As_partioned cnts_lth cnts_eq runnings
    
            let runnings' =  map6 (\ k cnt_lth cnt_eq cnt_gth running -> 
                                    if k <= cnt_lth && running
                                    then true
                                    else if k <= cnt_lth + cnt_eq || not running
                                    then false
                                    else true
                                  ) ks cnts_lth cnts_eq cnts_gth runnings

            -- We also need to calculate the new shape.
            let shp' = map5 (\ k cnt_lth cnt_eq cnt_gth running -> 
                                if k <= cnt_lth && running
                                then cnt_lth
                                else if k <= cnt_lth + cnt_eq || not running
                                then 0
                                else cnt_gth
                            ) ks cnts_lth cnts_eq cnts_gth runnings
            -- Nested loop parallelism version of As':
            -- let As' = map (\ k p A_partioned cnt_lth cnt_eq cnt_gth runnings -> 
            --                     if k <= cnt_lth && running
            --                     then
            --                         let is = iota cnt_lth
            --                         in map (\ i -> A_partioned[i])
            --                     else if k <= cnt_lth + cnt_eq || not running
            --                     then []
            --                     else
            --                         let is = map (\ i -> cnt_lth + cnt_eq + i) (iota cnt_gth)
            --                         in map (\i -> A_partioned[i])
            --         ) ks ps As_partioned cnts_lth cnts_eq cnts_gth
            -- Flattening, we can reuse ks', ps' and runnings' (no falttening needed)
            -- We just need to flatten As. Therefore we change to fit the form of the flattening rule:
            -- let lth_pred (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running) =
            --     k <= cnt_lth && running
            -- let lth_then (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running) =
            --     let is = iota cnt_lth
            --     in map (\ i -> A_partioned[i]) is
            -- let eq_pred (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running) =
            --     k <= cnt_lth + cnt_eq || not running
            -- let eq_then (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running) =
            --     []
            -- let eq_else (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running) =
            --     let is = map (\ i -> cnt_lth + cnt_eq + i) (iota cnt_gth)
            --     in map (\i -> A_partioned[i]) is
            -- let snd_if (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running) =
            --      if eq_pred (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running)
            --      then eq_then (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running)
            --      else eq_else (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running)
            -- let zipped_data = zip5 ks ps As_partioned (zip3 cnts_lth cnts_eq cnts_gth) runnings
            -- let As' = map (\ (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), runnings)
            --                 if lth_pred (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), runnings)
            --                 then lth_then (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), runnings)
            --                 else snd_if (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), runnings)
            --               ) zipped_data
            -- Flattening rule for if:
            -- F( map (\(x: a) : b -> if p x then f x else g x) xs ) =>
            -- ( [length xs],
            -- let len = length xs
            -- let (is, q) = partition2 (\i -> p (x[i])) (iota len)
            -- let (is_then, is_else ) = split q is
            -- let xs_then = map (\i_then -> xs[i_then]) is_then
            -- let res_then= F ( map f xs_then )
            -- let xs_else = map (\i_else -> xs[i_else]) is_else
            -- let res_else= F ( map g xs_else )
            -- let res = scatter (replicate len dummy) is_then xs_then
            -- in scatter res is_else xs_else
            -- )
            -- Now we flatten the if.
            let zipped_data = zip5 ks_expanded ps_expanded As_partioned (zip3 cnts_lth_expanded cnts_lth_plus_eq_expanded cnts_gth_expanded) runnings_expanded
            let len = len As_partioned
            let (is_lth, q_lth) = partition2 (\ i -> lth_pred zipped_data[i]) (iota len)
            let (is_then, is_else) = split q_lth is_lth
            let zipped_data_then = map (\ i_then -> zipped_data_then[i_then]) is_then
            -- let res_then = F (map lth_then xs_then) = map
            -- let res_then = F (map (\ (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running) ->
            --                         let lth_is = iota cnt_lth
            --                         in map (\ i -> A_partioned[i]) is
            --                    ) zipped_data_then)
            -- We do lopp distribution
            -- let res_then = 
            --     let lth_iss = F(map (\ cnt_lth ->
            --                             iota cnt_lth
            --                       ) cnts_lth) |> flatten
            --     in F(map2 (\ (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running) lth_is ->
            --                 map (\ i -> A_partioned[i]) lth_is
            --             ) zipped_data_then lth_iss) -- Here we can simply lift the outer map by expanding lth_iss
            -- Now we can flatten each of them:
            let res_then =
                let lth_iss =
                    let flag = mkFlagArray cnts_lth 0 (replicate 1 m)
                    let vals = map (\ f -> if f!=0 then 0 else 1) flag
                    in sgmScanInc (+) 0 flag vals
                in let row_offsets = (map (\ j -> if j == 0 then 0 else shp[j-1]) (iota (length shp))) |> scan (+) 0
                   let row_offsets_expanded =
                        let (flag_cnts_lth, flag_row_offsets) = zip cnts_lth row_offsets |> mkFlagArray cnts_lth (0,0) |> unzip
                        in sgmScanInc (+) 0 flag_cnts_lth flag_row_offsets
                   in map2 (\row_offset i -> As_partioned[row_offset+i]) row_offsets_expanded lth_iss
            let zipped_data_else = map (\i_else -> zipped_data[i_else]) is_else
            -- let res_else = F (map snd_if zipped_data_else)
            -- let res_else = F (map (\ ->
            --                         if eq_pred (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running)
            --                         then eq_then (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running)
            --                         else eq_else (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running)
            --                       ) zipped_data_else)
            let res_else =
                let len = length zipped_data_else
                let eq_pred (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running) =
                    k <= cnt_lth + cnt_eq || not running
                let (is_gth, q_gth) = partition2 (\ i -> eq_pred zipped_data_else[i]) (iota len)
                let (is_gth_then, is_gth_else) = split q_gth is_gth
                let zipped_data_else_then = map (\ i_gth_then -> zipped_data_else[i_gth_then]) is_gth_then
                -- let res_then = F (map eq_then zipped_data_else_then)
                -- let res_then = F (map (\ _ -> []) zipped_data_else_then)
                let res_else_then = []
                let zipped_data_else_else = map (\ i_gth_else -> zipped_data_else[i_gth_else]) is_gth_else
                -- let res_else = F (map eq_else zipped_data_else_else)
                -- let res_else = map (\ (k, p, A_partioned, (cnt_lth, cnt_eq, cnt_gth), running) ->
                --                     let is = map (\ i -> cnt_lth + cnt_eq + i) (iota cnt_gth)
                --                     in map (\i -> A_partioned[i]) is
                --                    ) zipped_data_else_else
                let res_else_else =
                    let gth_iss =
                        let flag = mkFlagArray cnts_gth 0 (replicate 1 m)
                        let vals = map (\ f -> if f!=0 then 0 else 1) flag
                        let iotas = sgmScanInc (+) 0 flag vals
                        let cnts_lth_eq_expanded =
                            let cnts_lth_eq = map2 (+) cnts_lth cnts_eq
                            let (flag_cnts_gth, flag_cnts_lth_eq) = zip cnts_gth cnts_lth_eq |> mkFlagArray cnts_gth (0,0) |> unzip
                            in sgmScanInc (+) 0 flag_cnts_gth flag_cnts_lth_eq
                        in map2 (+) iotas cnts_lth_eq_expanded
                    in let row_offsets = (map (\ j -> if j == 0 then 0 else shp[j-1]) (iota (length shp))) |> scan (+) 0
                    let row_offsets_expanded =
                        let (flag_cnts_gth, flag_row_offsets) = zip cnts_gth row_offsets |> mkFlagArray cnts_gth (0,0) |> unzip
                        in sgmScanInc (+) 0 flag_cnts_gth flag_row_offsets
                    in map2 (\row_offset i -> As_partioned[row_offset+i]) row_offsets_expanded gth_iss
                let res = scatter (replicate len 0) is_gth_then res_else_then
                in scatter res is_gth_else res_else_else
            
            let final_len = reduce (+) 0 shp' -- 
            let res = scatter (replicate final_len 0) is_then res_then -- This should probably not be len? but the new len of the new shape?
            let As' = scatter res is_else res_else

            in (ks', ps', shp', As', runnings')
    in ps



-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************
-- *********************************************************************************************************************************************************************





-- Human reasoning flattening:
let rankSearch (k: i64) (A: []f32) : f32 =
    let p = random_element A  -- This is part of what ensures expected O(n) given random distribution of data. Though we change this to length - 1 since it is easier to express.
    let p = (length A) - 1
    let A_lth_p = filter (< p) A
    let A_eq_p = filter (==p) A
    let A_gth_p = filter (> p) A in
    if (k <= A_lth_p.length)
        then rankSearch k A_lth_p
    else if (k <= A_lth_p.length + A_eq_p.length)
        then p
    else rankSearch (k - A_lth_p.length - A_eq_p.length) A_gth_p
let main [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 = map2 rankSearch ks As

-- We want to remove the tail recursion by using a while loop.
-- Instead of filtering at once we can split the filter up into 3 reduces and a single filter depending on which one we want to keep.
let nestedLoopRankSearch (k: i64) (A: []f32) : f32 =
    let (_, _, result) =
        loop (k, A, result) = (k, A, NAN)
        while length A > 0 do
            let p = A[(length A) - 1]
            -- let A_lth_p = filter (<  p) A
            let cnt_A_lth_p = reduce (+) 0 (map (\ e -> if e < p then 1 else 0)) A
            -- let A_eq_p = filter (== p) A
            let cnt_A_eq_p = reduce (+) 0 (map (\ e -> if e == p then 1 else 0)) A
            -- let A_gth_p = filter (>  p) A
            -- let cnt_A_gth_p = reduce (+) 0 (map (\ e if e > p then 1 else 0))

            in
            
            if (k <= cnt_A_lth_p)
            then (k, (filter (< p) A), result) -- Kind = 0
            else if (k <= cnt_A_lth_p + cnt_A_eq_p)
            then (k, [], p) -- Kind = 1
            else ((k - cnt_A_lth_p - cnt_A_eq_p), (filter (> p) A), result) -- Kind = 2
    in result

let main [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 = map2 rankSearch ks As

-- We extract a single iteration of the loop as a separate function
let nestedLoopRankSearchSingleIteration (k, A, result) =
    let p = if length A > 0 then A[(length A) - 1] else NAN
    let cnt_A_lth_p = reduce (+) 0 (map (\ e -> if e < p then 1 else 0)) A
    let cnt_A_eq_p = reduce (+) 0 (map (\ e -> if e == p then 1 else 0)) A
    in
    if (k <= cnt_A_lth_p)
    then (k, (filter (< p) A), result) -- Kind = 0
    else if (k <= cnt_A_lth_p + cnt_A_eq_p)
    then (k, [], p) -- Kind = 1
    else ((k - cnt_A_lth_p - cnt_A_eq_p), (filter (> p) A), result) -- Kind = 2

let nestedLoopRankSearch (k: i64) (A: []f32) : f32 =
    let (_, _, result) =
        loop (k, A, result) = (k, A, NAN)
        while length A > 0 do
            nestedLoopRankSearchSingleIteration (k, A, result)
    in result

let main [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 = map2 rankSearch ks As

-- Now we do the loop interchange (ASK COSMIN THIS BECAUSE WE ARE CHANGING THE CONDITION OF THE LOOP)
let nestedLoopRankSearchBatch [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 =
    let (_, _, results) =
        loop (ks, As, results) = (ks, As, (replicate m NAN))
        while (reduce (+) 0 (map length As)) > 0 do
            map nestedLoopRankSearchSingleIteration (zip3 ks As results)
            |> unzip3
    in result

-- Before we can distribute the map over the single iteration we need to change it slightly. Introducing kind.
let nestedLoopRankSearchSingleIteration (k, A, result) =
    let p = if length A > 0 then A[(length A) - 1] else NAN
    let cnt_A_lth_p = reduce (+) 0 (map (\ e -> if e < p then 1 else 0)) A
    let cnt_A_eq_p = reduce (+) 0 (map (\ e -> if e == p then 1 else 0)) A

    let kind = if length A == 0                       then -1 -- Was already done
               else if k <= cnt_A_lth_p              then  0 -- Less than direction
               else if k <= cnt_A_lth_p + cnt_A_eq_p then  1 -- Done
               else                                        2 -- Greater than direction
    let k' = if kind == 2 then (k - cnt_A_lth_p - cnt_A_eq_p) else k
    let A' = filter (\ elem ->
                        if      kind == 0 then elem < p -- Less than direction
                        else if kind == 1 then false -- Done
                        else                   elem > p -- Greater than direction
                    ) A
    let result' = if kind == 1 then p else result
    in
    (k', A', result')

    -- if (k <= cnt_A_lth_p)
    -- then (k, (filter (< p) A), result) -- Kind = 0
    -- else if (k <= cnt_A_lth_p + cnt_A_eq_p)
    -- then (k, [], p) -- Kind = 1
    -- else ((k - cnt_A_lth_p - cnt_A_eq_p), (filter (> p) A), result) -- Kind = 2

-- Distribute loop over nestedLoopRankSearchSingleIteration
let nestedLoopRankSearchBatch [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 =
    let (_, _, results) =
        loop (ks, As, results) = (ks, As, (replicate m NAN))
        while (reduce (+) 0 (map length As)) > 0 do
            let ps = map (\ A -> if length A > 0 then A[(length A) - 1] else NAN) As
            let cnts_lth_p = map2 (\ A p -> reduce (+) 0 (map (\ e -> if e < p then 1 else 0)) A) As ps
            let cnts_eq_p = map2 (\ A p -> reduce (+) 0 (map (\ e -> if e == p then 1 else 0)) A) As ps
            let kinds = map4 (\ A k cnt_lth cnt_eq ->
                                if length A > 0               then -1 -- Was already done
                                else if k <= cnt_lth          then  0 -- Less than direction
                                else if k <= cnt_lth + cnt_eq then  1 -- Done
                                else                                2 -- Greater than direction
                             ) As ks cnts_lth_p cnts_eq_p
            let ks' = map4 (\ kind k cnt_lth cnt_eq -> if kind == 2 then (k - cnt_lth - cnt_eq) else k) kinds ks cnts_lth_p cnts_eq_p
            let As' = map3 (\ A kind p -> filter(\ elem ->
                                                    if      kind == 0 then elem < p -- Less than direction
                                                    else if kind == 1 then false -- Done
                                                    else                   elem > p -- Greater than direction
                                                ) A) As kinds ps
            let results' = map3 (\ result kind p -> if kind == 1 then p else result) results kinds ps
            zip3 ks' As' results'
    in results

-- We can extract the inner-map from cnts_lth_p and cnts_eq_p into two different.
let nestedLoopRankSearchBatch [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 =
    let (_, _, results) =
        loop (ks, As, results) = (ks, As, (replicate m NAN))
        while (reduce (+) 0 (map length As)) > 0 do
            -- NOT FLAT
            let ps = map (\ A -> if length A > 0 then A[(length A) - 1] else NAN) As
            
            -- NOT FLAT
            -- WAS
            -- let cnts_lth_p = map2 (\ A p -> reduce (+) 0 (map (\ e -> if e < p then 1 else 0)) A) As ps
            -- let cnts_eq_p = map2 (\ A p -> reduce (+) 0 (map (\ e -> if e == p then 1 else 0)) A) As ps
            -- BECAME
            let ps_expanded = map2 (\ p A -> replicate (length A) p) ps As
            let cnt_lth_per_elem = map2 (map2 (\p e -> if e < p then 1 else 0)) As ps_expanded
            let cnt_eq_per_elem = map2 (map2 (\p e -> if e == p then 1 else 0)) As ps_expanded
            let cnts_lth_p = map (reduce (+) 0) cnt_lth_per_elem
            let cnts_eq_p = map (reduce (+) 0) cnt_eq_per_elem
            
            -- FLAT
            let kinds = map4 (\ A k cnt_lth cnt_eq ->
                                if length A > 0               then -1 -- Was already done
                                else if k <= cnt_lth          then  0 -- Less than direction
                                else if k <= cnt_lth + cnt_eq then  1 -- Done
                                else                                2 -- Greater than direction
                             ) As ks cnts_lth_p cnts_eq_p
            
            -- FLAT
            let ks' = map4 (\ kind k cnt_lth cnt_eq -> if kind == 2 then (k - cnt_lth - cnt_eq) else k) kinds ks cnts_lth_p cnts_eq_p

            -- NOT FLAT
            let As' = map3 (\ A kind p -> filter(\ elem ->
                                                    if      kind == 0 then elem < p -- Less than direction
                                                    else if kind == 1 then false -- Done
                                                    else                   elem > p -- Greater than direction
                                                ) A ) As kinds ps
            
            --FLAT
            let results' = map3 (\ result kind p -> if kind == 1 then p else result) results kinds ps
            zip3 ks' As' results'
    in results

-- Now we begin to flatten the different nested list parallelisms. Therefore we make As flat and give along a shape.
-- When values are filtered from As we need to have shp change accordingly. We can observe that based on the kind we
-- know what that subarray will be after the filter. Ie. kind == 0 (elements less than), kind == 1 (were done therefore  0),
-- kind == 2 (elements greater than => new_size = cur_size - elements less than - elements equal)
-- Ie. let shp' = map4 (\ len kind lth eq->
--                          if kind ==  0      then lth
--                          else if kind ==  1 then 0
--                          else len - (lth + eq)
--                      ) shp kinds cnt_lth cnt_eq
-- We flatten the map (replicate), map (map), map (reduce)

let nestedLoopRankSearchBatch [m] [n] (ks: [m]i64) (As: [n]f32) (shp : [m]i32): [m]f32 =
    let (_, _, results) =
        loop (ks, shp, As, results) = (ks, shp, As, (replicate m NAN))
        --while (reduce (+) 0 (map length As)) > 0 do
        while (length As) > 0 do
            -- FLAT
            -- let ps = map (\ A -> if length A > 0 then A[(length A) - 1] else NAN) As
            let ps = map2 (\ i size -> if size > 0 then A[i - 1] else NAN) (scan (+) 0 shp) shp

            -- WAS NOT FLAT
            -- let ps_expanded = map2 (\ p A -> replicate (length A) p) ps As
            -- WE MAKE IT USE THE SHAPE
            -- let ps_expanded = map2 (\size p -> replicate size p) shp ps
            -- NOW IT IS FLAT
            let (flag_shp,flag_ps) = zip shp ps |> mkFlagArray shp (0,0) |> unzip
            let ps_expanded = sgmScanInc (+) 0 flag_shp flag_ps

            
            -- let cnt_lth_per_elem = map2 (map2 (\p e -> if e < p then 1 else 0)) As ps_expanded
            let cnt_lth_per_elem = map2 (\p e -> if e < p then 1 else 0) As ps_expanded

            -- let cnt_eq_per_elem = map2 (map2 (\p e -> if e == p then 1 else 0)) As ps_expanded
            let cnt_eq_per_elem = map2 (\p e -> if e == p then 1 else 0) As ps_expanded
            
            
            
            -- Flatten for map reduce
            -- F( map (\ row -> reduce ⊙ e⊙ row) mat )⇒
            -- let mat_flg'= mkFlagArray mat_shp 0 (replicate num_rows true)
            -- let mat_flg = mat_flg' :> [n]bool -- dynamic size cast
            -- let sc_mat = sgmScanInc ⊙ e⊙ mat_flg mat_val
            -- let indsp1 = scaninc (+) 0 mat_shp
            -- let res = map2 (\shp ip1 -> if shp==0 then e⊙ else sc_mat[ip1 -1]
            -- ) mat_shp indsp1 in ( num_rows , res )

            -- WAS NOT FLAT
            -- let cnts_lth_p = map (reduce (+) 0) cnt_lth_per_elem
            -- let cnts_eq_p = map (reduce (+) 0) cnt_eq_per_elem
            -- NOW IT IS FLAT
            let mat_flg' = mkFlagArray shp 0 (replicate m true)
            let mat_flg = mat_flag' :> [n]bool
            let sc_mat_lth = sgmScanInc (+) 0 mat_flg cnt_lth_per_elem -- sgmScanInc may not be totally well formed at this point because of the differing types.
            let sc_mat_eq = sgmScanInc (+) 0 mat_flg cnt_eq_per_elem
            let indsp1 = scan (+) 0 shp
            let cnts_lth_p = map2 (\ size ip1 -> if size == 0 then 0 else sc_mat_lth[ip-1]) shp indsp1
            let cnts_eq_p = map2 (\ size ip1 -> if size == 0 then 0 else sc_mat_eq[ip-1]) shp indsp1

            -- FLAT
            -- let kinds = map4 (\ A k cnt_lth cnt_eq ->
            --                     if length A > 0               then -1 -- Was already done
            --                     else if k <= cnt_lth          then  0 -- Less than direction
            --                     else if k <= cnt_lth + cnt_eq then  1 -- Done
            --                     else                                2 -- Greater than direction
            --                  ) As ks cnts_lth_p cnts_eq_p
            let kinds = map4 (\ size k cnt_lth cnt_eq ->
                                if size > 0               then -1 -- Was already done
                                else if k <= cnt_lth          then  0 -- Less than direction
                                else if k <= cnt_lth + cnt_eq then  1 -- Done
                                else                                2 -- Greater than direction
                             ) shp ks cnts_lth_p cnts_eq_p

            
            -- FLAT
            let ks' = map4 (\ kind k cnt_lth cnt_eq -> if kind == 2 then (k - cnt_lth - cnt_eq) else k) kinds ks cnts_lth_p cnts_eq_p

            -- WAS NOT FLAT
            -- let As' = map3 (\ A kind p -> filter(\ elem ->
            --                                         if      kind == 0 then elem < p -- Less than direction
            --                                         else if kind == 1 then false -- Done
            --                                         else                   elem > p -- Greater than direction
            --                                     ) A ) As kinds ps
            -- REWRITING TO WORK WITH THE FLAT DAT BUT STILL HAVING A NESTED LOOP PARALLELISM (map (replicate))
            -- let kinds_expanded = map2 (\ size -> replicate size p) shp ps
            -- let (_, _, As') = filter (\ elem kind p ->
            --                             if      kind == 0 then elem < p -- Less than direction
            --                             else if kind == 1 then false -- Done
            --                             else                   elem > p -- Greater than direction
            --                          ) (zip3 As kinds_expanded ps_expanded)
            --                     |> unzip3
            -- NOW IT IS FLAT
            let (flag_shp,flag_kinds) = zip shp kinds |> mkFlagArray shp (0,0) |> unzip
            let kinds_expanded = sgmScanInc (+) 0 flag_shp flag_kinds
            let (_, _, As') = filter (\ elem kind p ->
                                        if      kind == 0 then elem < p -- Less than direction
                                        else if kind == 1 then false -- Done
                                        else                   elem > p -- Greater than direction
                                     ) (zip3 As kinds_expanded ps_expanded)
                                |> unzip3
            
            --FLAT
            let shp' = map4 (\ len kind lth eq->
                         if kind ==  0      then lth
                         else if kind ==  1 then 0
                         else len - (lth + eq)
                     ) shp kinds cnt_lth cnt_eq
            
            --FLAT
            let results' = map3 (\ result kind p -> if kind == 1 then p else result) results kinds ps
            zip4 ks' shp' As' results'
    in results

-- The above uses the flattening transformations.
-- Reasoning like a human we can determine that ps_expanded as well as kinds_expanded
-- (which were map (replicate)) could be expressed alternately in their nested loop parallel form as:
-- let ps_expanded = map2 (\ size i -> replicate size ps[i]) shp (iota m)
-- let kinds_expanded = map2 (\size i -> replicate size kinds[i]) shp (iota m)
-- This would allow them to use in their flattened form the same expanded "flag" array.
-- The flattening results in an array of row indices "expanded" II1.
-- cnts_lth_p & cnts_eq_p are in their nested loop parallel form map (reduce) which we now can
-- replace with a reduce_by_index since we are just tallying up the ones set in cnt_..._per_elem.

let nestedLoopRankSearchBatch [m] [n] (ks: [m]i64) (As: [n]f32) (shp : [m]i32): [m]f32 =
    let (_, _, results) =
        loop (ks, shp, As, results) = (ks, shp, As, (replicate m NAN))
        while (length As) > 0 do

            let ps = map2 (\ i size -> if size > 0 then A[i - 1] else NAN) (scan (+) 0 shp) shp

            -- Alternate nested loop parallel formulation:
            -- let ps_expanded = map2 (\ size i -> replicate size ps[i]) shp (iota m)
            -- Flattened:
            let (flag_shp, flag_i) = zip shp (iota m) |> mkFlagArray shp (0,0) |> unzip
            let II1 = sgmScanInc (+) 0 flag_shp flag_i
            let ps_expanded = map (\ i -> ps[i]) II1
            

            let cnt_lth_per_elem = map2 (\p e -> if e < p then 1 else 0) As ps_expanded
            let cnt_eq_per_elem = map2 (\p e -> if e == p then 1 else 0) As ps_expanded
            
            let cnt_lth = reduce_by_index (replicate m (0)) (+) (0) II1 cnt_lth_per_elem
            let cnt_eq = reduce_by_index (replicate m (0)) (+) (0) II1 cnt_eq_per_elem            

            let kinds = map4 (\ size k cnt_lth cnt_eq ->
                                if size > 0                   then -1 -- Was already done
                                else if k <= cnt_lth          then  0 -- Less than direction
                                else if k <= cnt_lth + cnt_eq then  1 -- Done
                                else                                2 -- Greater than direction
                             ) shp ks cnts_lth_p cnts_eq_p

            let ks' = map4 (\ kind k cnt_lth cnt_eq -> if kind == 2 then (k - cnt_lth - cnt_eq) else k) kinds ks cnts_lth_p cnts_eq_p

            -- Alternate nested loop parallel formulation:
            -- let kinds_expanded = map2 (\ size i -> replicate size kinds[i]) shp (iota m)
            -- Flattened: (Reusing II1) from earlier
            -- let kinds_expanded = map (\ i -> kinds[i]) II1
            -- let (_, _, As') = filter (\ elem kind p ->
            --                             if      kind == 0 then elem < p -- Less than direction
            --                             else if kind == 1 then false -- Done
            --                             else                   elem > p -- Greater than direction
            --                          ) (zip3 As kinds_expanded ps_expanded)
            --                     |> unzip3
            -- Since we only use kinds_expanded in the calculation of As' we can simply put the lookup into the filter:
            let (_, _, As') = filter (\ elem i p ->
                                        let kind = kinds[i] in
                                        if      kind == 0 then elem < p -- Less than direction
                                        else if kind == 1 then false -- Done
                                        else                   elem > p -- Greater than direction
                                     ) (zip3 As II1 ps_expanded)
                                |> unzip3

            let shp' = map4 (\ len kind lth eq->
                                if kind ==  0      then lth
                                else if kind ==  1 then 0
                                else len - (lth + eq)
                            ) shp kinds cnt_lth cnt_eq
                    
            let results' = map3 (\ result kind p -> if kind == 1 then p else result) results kinds ps
            zip4 ks' shp' As' results'
    in results

-- Since the II1 will only change in the same way as As' does (ie. the elements at the same position that are kept from As should also be kept from II1')
-- Therefore we can take the calculation of II1 outside the loop and just add it to the loop state.
-- or remove the calculation of II1 from the function entirely by taking it as a parameter.
-- Given these two transformations we are basically at the human reasoning version from the project description.
let nestedLoopRankSearchBatch [m] [n] (ks: [m]i64) (shp : [m]i32) (II1 : [n]i32) (As: [n]f32) : [m]f32 =
    let (_, _, results) =
        loop (ks, shp, As, results) = (ks, shp, As, (replicate m NAN))
        while (length As) > 0 do

            let ps = map2 (\ i size -> if size > 0 then A[i - 1] else NAN) (scan (+) 0 shp) shp

            -- Alternate nested loop parallel formulation:
            -- let ps_expanded = map2 (\ size i -> replicate size ps[i]) shp (iota m)
            -- Flattened:
            let (flag_shp, flag_i) = zip shp (iota m) |> mkFlagArray shp (0,0) |> unzip
            let II1 = sgmScanInc (+) 0 flag_shp flag_i
            let ps_expanded = map (\ i -> ps[i]) II1

            let cnt_lth_per_elem = map2 (\p e -> if e < p then 1 else 0) As ps_expanded
            let cnt_eq_per_elem = map2 (\p e -> if e == p then 1 else 0) As ps_expanded
            
            let cnt_lth = reduce_by_index (replicate m (0)) (+) (0) II1 cnt_lth_per_elem
            let cnt_eq = reduce_by_index (replicate m (0)) (+) (0) II1 cnt_eq_per_elem            

            let kinds = map4 (\ size k cnt_lth cnt_eq ->
                                if size > 0                   then -1 -- Was already done
                                else if k <= cnt_lth          then  0 -- Less than direction
                                else if k <= cnt_lth + cnt_eq then  1 -- Done
                                else                                2 -- Greater than direction
                             ) shp ks cnts_lth_p cnts_eq_p

            let ks' = map4 (\ kind k cnt_lth cnt_eq -> if kind == 2 then (k - cnt_lth - cnt_eq) else k) kinds ks cnts_lth_p cnts_eq_p

            -- Alternate nested loop parallel formulation:
            -- let kinds_expanded = map2 (\ size i -> replicate size kinds[i]) shp (iota m)
            -- Flattened: (Reusing II1) from earlier
            -- let kinds_expanded = map (\ i -> kinds[i]) II1
            -- let (_, _, As') = filter (\ elem kind p ->
            --                             if      kind == 0 then elem < p -- Less than direction
            --                             else if kind == 1 then false -- Done
            --                             else                   elem > p -- Greater than direction
            --                          ) (zip3 As kinds_expanded ps_expanded)
            --                     |> unzip3
            -- Since we only use kinds_expanded in the calculation of As' we can simply put the lookup into the filter:
            let (_, _, As') = filter (\ elem i p ->
                                        let kind = kinds[i] in
                                        if      kind == 0 then elem < p -- Less than direction
                                        else if kind == 1 then false -- Done
                                        else                   elem > p -- Greater than direction
                                     ) (zip3 As II1 ps_expanded)
                                |> unzip3

            let shp' = map4 (\ len kind lth eq->
                                if kind ==  0      then lth
                                else if kind ==  1 then 0
                                else len - (lth + eq)
                            ) shp kinds cnt_lth cnt_eq
            
            let results' = map3 (\ result kind p -> if kind == 1 then p else result) results kinds ps
            zip4 ks' shp' As' results'
    in results

-- On this we can do a number of optimizations.