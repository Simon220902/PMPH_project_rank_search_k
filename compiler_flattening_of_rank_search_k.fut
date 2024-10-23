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
--     let A_eqt_p = filter (==p) A
--     let A_gth_p = filter (> p) A
--     if (k <= A_lth_p.length)
--         then rankSearch k A_lth_p
--     else if (k <= A_lth_p.length + A_eqt_p.length)
--         then p
--     else rankSearch (k - A_lth_p.length - A_eqt_p.length) A_gth_p
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
            let A_eqt_p = filter (== p) A
            let A_gth_p = filter (>  p) A in
            if (k <= (length A_lth_p))
            then (k, A_lth_p[(length A_lth_p) -1], A_lth_p, true)
            else if (k <= (length A_lth_p) + (length A_eqt_p))
            then (k, p, A, false)
            else ((k - (length A_lth_p) - (length A_eqt_p)), A_gth_p[(length A_gth_p)-1], A_gth_p, true)
    in p

let main [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 = map2 rankSearch ks As

-- Now we want to switch the loop and map2.
-- This means that we do one iteration for each of the arrays. The condition now is whether there is a running variable that is true (i.e. reduce (or) false array_of_running).
-- Since the outer loop is now doing it for all the different arrays in the batch we need to expand the tuple being updated in the while loop.
-- 
let oneStepRankSearch (k: i64, p:f32, A: []f32, running: bool) : (i64, f32, []f32, bool) =
    if running then
        let A_lth_p = filter (<  p) A
        let A_eqt_p = filter (== p) A
        let A_gth_p = filter (>  p) A in
        if (k <= (length A_lth_p))
        then (k, A_lth_p[(length A_lth_p) -1], A_lth_p, true)
        else if (k <= (length A_lth_p) + (length A_eqt_p))
        then (k, p, A, false)
        else ((k - (length A_lth_p) - (length A_eqt_p)), A_gth_p[(length A_gth_p)-1], A_gth_p, true)
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
    let A_eqt_p = filter (==p) A
    let A_gth_p = filter (> p) A in
    if (k <= A_lth_p.length)
        then rankSearch k A_lth_p
    else if (k <= A_lth_p.length + A_eqt_p.length)
        then p
    else rankSearch (k - A_lth_p.length - A_eqt_p.length) A_gth_p
let main [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 = map2 rankSearch ks As

-- We want to remove the tail recursion by using a while loop.
-- Instead of filtering at once we can split the filter up into 3 reduces and a single filter depending on which one we want to keep.
entry nestedLoopRankSearch (k: i64) (A: []f32) : f32 =
    let (_, _, result) =
        loop (k, A, result) = (k, A, -INFINITY)
        while length A > 0 do
            let p = A[(length A) - 1]
            -- let A_lth_p = filter (<  p) A
            let cnt_A_lth_p = reduce (+) 0 (map (\ e if e < p then 1 else 0))
            -- let A_eqt_p = filter (== p) A
            let cnt_A_eqt_p = reduce (+) 0 (map (\ e if e == p then 1 else 0))
            -- let A_gth_p = filter (>  p) A
            let cnt_A_gth_p = reduce (+) 0 (map (\ e if e > p then 1 else 0))

            in
            
            if (k <= cnt_A_lth_p)
            then (k, (filter (< p) A), result) -- Kind = 0
            else if (k <= cnt_A_lth_p + cnt_A_eqt_p)
            then (k, [], p) -- Kind = 1
            else ((k - cnt_A_lth_p - cnt_A_eqt_p), (filter (> p) A), result) -- Kind = 2
    in result

let main [m] (ks: [m]i64) (As: [m][]f32) : [m]f32 = map2 rankSearch ks As

-- To do the loop interchange first rewrite the map2 as a loop?
let nestedBatchedLoopRankSearch (ks: [m]i64) (As: [m][]f32) : [m]f32 =
    -- The map
    let results = replicate -INFINITY m
    let (_, results) =
        loop (i, results) = (0, results)
        while (i < m) do
        let result = nestedLoopRankSearch ks[i] As[i]
        in (i+1, (scatter results [i] [result]))
    in results

-- Now we need to do loop distribution???? Or should we just have distributed the map doing array expansion?
-- But which arrays is it that need to be expanded?
