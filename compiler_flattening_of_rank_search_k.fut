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
let oneStepRankSearch (k: i64, p:f32, A: []f32, running: bool) : (i64, f32, []f32, bool) =
    if running then
        let A_lth_p = filter (<  p) A
        let A_eq_p = filter (== p) A
        let A_gth_p = filter (>  p) A in
        if (k <= (length A_lth_p))
        then (k, A_lth_p[(length A_lth_p) -1], A_lth_p, true)
        else if (k <= (length A_lth_p) + (length A_eq_p))
        then (k, p, A, false)
        else ((k - (length A_lth_p) - (length A_eq_p)), A_gth_p[(length A_gth_p)-1], A_gth_p, true)
    else (k, p, A, running)

let batchNestedRankSearch [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 =
    let ps = map (\ A -> A[(length A)-1]) As
    let runnings = replicate true m

    let (_, ps, _, _) =
        loop (ks, ps, As, runnings) = (ks, ps, As, runnings)
        while (reduce (or) false runnings) do
            zip4 ks ps As runnings
            |> map oneStepRankSearch
            |> unzip4
    
    

--                                                         MAYBE NOT?
let nestedLooprankSearchBatch (ks: [m]i32) (shp: [m]i32) (II1: *[n]i32) (A: [n]f32) : *[m]f32 =

  

-- Questions for Cosmin:
-- -- We have written a version using the loop as you described instead of the tail-recursion,
   -- though we can not really figure out how we should think of this in terms of flattening.
   -- The loop introduces a "necessarily" sequential number of steps. Is it just the loop-swapping? since map2 is parallel?






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

    let kind = if length A > 0                       then -1 -- Was already done
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
            -- FLAT
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
