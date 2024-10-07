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
-- We can switch 
-- Questions for Cosmin:
-- -- We have written a version using the loop as you described instead of the tail-recursion,
   -- though we can not really figure out how we should think of this in terms of flattening.
   -- The loop introduces a "necessarily" sequential number of steps. Is it just the loop-swapping? since map2 is parallel?

