import "lib/github.com/diku-dk/sorts/radix_sort"

-- Radix sort based Rank search K
-- ==

-- entry: radix_sort_based_rank_search_k
-- input {4i64 [1f32, 2f32, 3f32, 4f32, 5f32, 6f32, 7f32, 8f32, 9f32, 10f32, 11f32, 12f32]}
-- output { 4f32 }
-- random input { 50000i64 [100000]f32 }
-- random input { 500000i64 [1000000]f32 }
entry radix_sort_based_rank_search_k (k: i32) (A: []f32) : f32 =
  let sorted_array = radix_sort f32.num_bits f32.get_bit A in
  sorted_array[k-1]

-- Radix sort based Rank search K
-- ==


-- entry: radixSortRankSearchBatch
-- input {[4i32] [12i32] [1f32, 2f32, 3f32, 4f32, 5f32, 6f32, 7f32, 8f32, 9f32, 10f32, 11f32, 12f32]}
-- output { [4f32] }

entry radixSortRankSearchBatch [m] [n] (ks: [m]i32) (shp: [m]i32) (A: [n]f32) : [m]f32 =
    let shp = map i64.i32 shp
    let start_indices = map (\ elem -> elem - shp[0]) (scan (+) 0 shp) in
    map3 (\ k size i0 ->
            let a = map (\ i -> A[i+i0]) (iota size) in -- A[i0:(i0+size)] in -- We don't know whether a slize or a map-iota are better?
            radix_sort_based_rank_search_k k a
         ) ks shp start_indices


-- Nested Loop Rank search K
-- ==

-- entry: nestedLoopRankSearch
-- input {4i64 [1f32, 2f32, 3f32, 4f32, 5f32, 6f32, 7f32, 8f32, 9f32, 10f32, 11f32, 12f32]}
-- output { 4f32 }
-- random input { 50000i64 [100000]f32 }
-- random input { 500000i64 [1000000]f32 }

-- input {4i64 [7f32, 8f32, 1f32, 5f32, 6f32, 9f32, 10f32, 11f32, 12f32, 2f32, 3f32, 4f32]}
-- output { 4f32 }
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



-- Human Reasoning Version

-- ==


-- entry: rankSearchBatch
-- input {[4i32] [12i32] [0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32] [1f32, 2f32, 3f32, 4f32, 5f32, 6f32, 7f32, 8f32, 9f32, 10f32, 11f32, 12f32]}
-- output { [4f32] }

entry rankSearchBatch [m] [n] (ks: [m]i32) (shp: [m]i32)
                    (II1: *[n]i32) (A: [n]f32) : [m]f32 =
    let result = replicate m 0f32
    -- let ks = map id ks
    -- let shp = map id shp
    -- let A = map id A

    -- FOR BETTER PERFORMANCE:
    -- We can treat the first iteration differently. By choosing the pivot as the average of that array.

    let (_,_,_,_,result) =
        loop (ks: [m]i32, shp: [m]i32, II1, A, result)
        while (length A > 0) do
            -- 1. compute the pivot for each subproblem, e.g., by choosing the
            -- last element. This is a small parallel operation of size m.
            let ps = map2 (\ i size -> if size > 0 then A[i-1] else 0) (scan (+) 0 shp) shp
            -- 2. for each subproblem compute the number of elements less than or equal to the pivot.
            -- This is a large-parallel operation of size n.
            -- Hint: use a histogram or reduce_by_index construct.
            let ps_expanded = map (\i -> ps[i]) II1
            --let lth_per_elem = map2 (\ elem p -> if elem < p then 1 else 0) A ps_expanded
            --let eq_per_elem = map2 (\ elem p -> if elem == p then 1 else 0) A ps_expanded
            let lth_eq_per_elem = map2 (\ elem p -> (if elem < p then (1,0) else if elem == p then (0,1) else (0,0))) A ps_expanded
            let II1' = map i64.i32 II1
            --let cnt_lth = reduce_by_index (replicate m (0)) (+) (0) II1' lth_per_elem
           -- let cnt_eq = reduce_by_index (replicate m (0)) (+) (0) II1' eq_per_elem
           let (cnt_lth, cnt_eq) = reduce_by_index (replicate m (0, 0)) (\ (a, b) (c, d) -> (a+c, b+d)) (0, 0) II1' lth_eq_per_elem |> unzip

            -- 3. Use a small-parallel operation of size m to compute:
            --     3.1 kinds → the kind of each subproblem, e.g.,
            --     (a) -1 means that this subproblem was already solved
            --     (b) 0  means that it should recurse in “< pivot” dir
            --     (c) 1  means that the base case was reached
            --     (d) 2  means that it should recurse in “> pivot” dir
            let kinds = map3 (\ k lth eq->
                                if k == -1            then -1
                                else if k <= lth      then  0
                                else if k <= (lth+eq) then  1
                                else                        2
                            ) ks cnt_lth cnt_eq

            --     3.2 shp’ → the new shape after this iteration, e.g., if
            --             we just discovered kinds==1 for some subproblem
            --             then we should set the corresponding element of
            --             shp’ to zero.
            let shp' = map4 (\ len kind lth eq->
                                if      kind == -1 then len
                                else if kind ==  0 then lth
                                else if kind ==  1 then 0
                                else len - (lth + eq)
                            ) shp kinds cnt_lth cnt_eq
            
            --     3.3 ks’  → the new value of k for each subproblem
            --             (the inactive subproblems may use -1 or similar)
            let ks' = map4  (\ k kind lth eq ->
                                if      kind == -1 then -1
                                else if kind ==  0 then k
                                else if kind ==  1 then -1
                                else k - (lth + eq)                -- if kind ==  2 then k - leq
                            ) ks kinds cnt_lth cnt_eq

            -- 4. write to result the solutions of the subproblems that have
            --     just finished (have kinds 1)
            -- let result = map3 (\ res kind p ->
            --                     if kind == 1 then p
            --                     else res
            --                   ) result kinds ps
            let (_, is, vs) = filter (\(kind, _, _) -> kind == 1) (zip3 kinds (iota m) ps) |> unzip3
            let result' = scatter result is vs
            
            -- 5. filter the A and II1 arrays to contain only the elements of
            --     interest of the subproblems that are still active.
            
            -- let (_, _, A', II1') = zip4 lth_per_elem eq_per_elem A II1
            let (_, A', II1') = zip3 lth_eq_per_elem A II1
                            |> filter (\ ((lth, eq), _, i) ->
                                        let kind = kinds[i] in
                                        if kind == -1 then false
                                        else if kind == 0 then lth == 1
                                        else if kind == 1 then false
                                        else lth == 0 && eq == 0
                                )
                            |> unzip3
                            -- -- |> unzip4
            in (ks', shp', II1', A', result')
    in result






-- N = 100000000 M = 10000 --> that our "n" should be N / M


-- Human Reasoning Version Test large inputs
-- ==
-- entry: testRankSearchBatch
-- random input { [10000][10000]f32 }
entry testRankSearchBatch [m] [n] (A : [m][n]f32) : [m]f32 =
    -- let m_elem = i32.i64 m
    let n_elem = i32.i64 n
    let A = flatten A
    let II1 = map (\i -> replicate n i) (iota m) |> flatten |> map i32.i64
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    in rankSearchBatch ks shp II1 A

-- Radix Sort Version Test large inputs
-- ==
-- entry: testRadixSortRankSearchBatch
-- random input { [10000][10000]f32 }
entry testRadixSortRankSearchBatch [m] [n] (A : [m][n]f32) : [m]f32 =
    let n_elem = i32.i64 n
    let A = flatten A
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    in radixSortRankSearchBatch ks shp A