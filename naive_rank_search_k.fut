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
    -- Can't generalize optimized to type variable 't because: https://futhark-book.readthedocs.io/en/latest/language.html#parametric-polymorphism "Hence, the Futhark compiler will prevent us from using the + operator. In some languages, such as Haskell, facilities such as type classes may be used to support a notion of restricted polymorphism, where we can require that an instantiation of a type variable supports certain operations (like +)."
    -- Also you can't overload a function: https://futhark.readthedocs.io/en/latest/language-reference.html "Overloaded operators cannot be defined by the user."
    let result = replicate m 0f32
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


-- entry: rankSearchBatchOptimized

-- input {[4i32] [12i32] [0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32] [1f32, 2f32, 3f32, 4f32, 5f32, 6f32, 7f32, 8f32, 9f32, 10f32, 11f32, 12f32]}
-- output { [4f32] }
entry rankSearchBatchOptimized [m] [n] (ks: [m]i32) (shp: [m]i32)
                    (II1: *[n]i32) (A: [n]f32) : [m]f32 =
    let result = replicate m 0f32
    let II1' = map i64.i32 II1
    let i = 0
    let (_,_,_,_,_,result) =
        loop (i : i32, ks: [m]i32, shp: [m]i32, II1', A, result)
        while (length A > 0) do
            let ps = if i == 0 then
                        map2 (\ sum len -> sum / len) (reduce_by_index (replicate m (0)) (+) (0) II1' A) (map f32.i32 shp)
                    else map2 (\ i size -> if size > 0 then A[i-1] else 0) (scan (+) 0 shp) shp
            let ps_expanded = map (\i -> ps[i]) II1'
            let lth_eq_per_elem = map2 (\ elem p -> (if elem < p then (1i32,0i32) else if elem == p then (0i32,1i32) else (0i32,0i32))) A ps_expanded
            let (cnt_lth, cnt_eq) = reduce_by_index (replicate m (0, 0)) (\ (a, b) (c, d) -> (a+c, b+d)) (0, 0) II1' lth_eq_per_elem |> unzip

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
            
            let (_, A', II1') = zip3 lth_eq_per_elem A II1'
                            |> filter (\ ((lth, eq), _, i) ->
                                        let kind = kinds[i] in
                                        if kind == -1 then false
                                        else if kind == 0 then lth == 1
                                        else if kind == 1 then false
                                        else lth == 0 && eq == 0
                                )
                            |> unzip3
            in (i+1, ks', shp', II1', A', result')
    in result

-- entry: rankSearchBatchOptimizedFirstIterationOut

-- input {[4i32] [12i32] [0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32, 0i32] [1f32, 2f32, 3f32, 4f32, 5f32, 6f32, 7f32, 8f32, 9f32, 10f32, 11f32, 12f32]}
-- output { [4f32] }
entry rankSearchBatchOptimizedFirstIterationOut [m] [n] (ks: [m]i32) (shp: [m]i32)
                    (II1: *[n]i32) (A: [n]f32) : [m]f32 =
    let result = replicate m 0f32
    let II1' = map i64.i32 II1
    -- First iteration taken out of the loop
    let ps_fst = map2 (\ sum len -> sum / len) (reduce_by_index (replicate m (0)) (+) (0) II1' A) (map f32.i32 shp)
    let ps_expanded_fst = map (\i -> ps_fst[i]) II1'
    let lth_eq_per_elem_fst = map2 (\ elem p -> (if elem < p then (1i32,0i32) else if elem == p then (0i32,1i32) else (0i32,0i32))) A ps_expanded_fst
    let (cnt_lth, cnt_eq) = reduce_by_index (replicate m (0, 0)) (\ (a, b) (c, d) -> (a+c, b+d)) (0, 0) II1' lth_eq_per_elem_fst |> unzip
    let kinds = map3 (\ k lth eq->
                                if k == -1            then -1i8
                                else if k <= lth      then 0i8
                                else if k <= (lth+eq) then 1i8
                                else                       2i8
                            ) ks cnt_lth cnt_eq
    
    let (shp_fst, ks_fst) = map5 (\ len k kind lth eq->
                                        if      kind == -1i8 then (len, -1)
                                        else if kind ==  0i8 then (lth, k)
                                        else if kind ==  1i8 then (0, -1)
                                        else (len - (lth + eq), k - (lth + eq))
                                    ) shp ks kinds cnt_lth cnt_eq
                              |> unzip
    
    let (_, is, vs) = filter (\(kind, _, _) -> kind == 1i8) (zip3 kinds (iota m) ps_fst) |> unzip3
    let result_fst = scatter result is vs
    let (_, A_fst, II1_fst) = zip3 lth_eq_per_elem_fst A II1'
                            |> filter (\ ((lth, eq), _, i) ->
                                        let kind = kinds[i] in
                                        if kind == -1 then false
                                        else if kind == 0 then lth == 1
                                        else if kind == 1 then false
                                        else lth == 0 && eq == 0
                                )
                            |> unzip3
    
    let (_,_,_,_,result) =
        loop (ks: [m]i32, shp: [m]i32, II1', A, result) = ((copy ks_fst), shp_fst, (copy II1_fst), A_fst,  result_fst)
        while (length A > 0) do
            let ps = map2 (\ i size -> if size > 0 then A[i-1] else 0) (scan (+) 0 shp) shp

            let ps_expanded = map (\i -> ps[i]) II1'
            let lth_eq_per_elem = map2 (\ elem p -> (if elem < p then (1i32,0i32) else if elem == p then (0i32,1i32) else (0i32,0i32))) A ps_expanded
            -- Tried the below "optimization" of not generating a ps_expandend. It did not do a difference.
            -- let lth_eq_per_elem = map2 (\ elem i -> (if elem < ps[i] then (1i32,0i32) else if elem == ps[i] then (0i32,1i32) else (0i32,0i32))) A II1'
            let (cnt_lth, cnt_eq) = reduce_by_index (replicate m (0, 0)) (\ (a, b) (c, d) -> (a+c, b+d)) (0, 0) II1' lth_eq_per_elem |> unzip
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

            let (_, A', II1') = zip3 lth_eq_per_elem A II1'
                            |> filter (\ ((lth, eq), _, i) ->
                                        let kind = kinds[i] in
                                        if kind == -1 || kind == 1 then false
                                        else if kind == 0 then lth == 1
                                        else lth == 0 && eq == 0
                                )
                            |> unzip3
            in (ks', shp', II1', A', result')
    in result

-- N = 100000000 M = 10000 --> that our "n" should be N / M
-- CUB VERSION RAN IN: 5904.29 us

-- Human Reasoning Version Test large inputs
-- ==
-- entry: testRankSearchBatch

-- random input { [10000][100]f32 }
-- random input { [1000000][100]f32 }
-- random input { [10000][10000]f32 }
-- random input { [1000][100000]f32}
entry testRankSearchBatch [m] [n] (A : [m][n]f32) : [m]f32 =
    -- let m_elem = i32.i64 m
    let n_elem = i32.i64 n
    let A = flatten A
    let II1 = map (\i -> replicate n i) (iota m) |> flatten |> map i32.i64
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    in rankSearchBatch ks shp II1 A

-- Human Reasoning Version Optimized Test large inputs
-- ==

-- -- entry: testRankSearchBatchOptimized

-- random input { [10000][100]f32 }
-- random input { [1000000][100]f32 }
-- random input { [10000][10000]f32 }
-- random input { [1000][100000]f32}
entry testRankSearchBatchOptimized [m] [n] (A : [m][n]f32) : [m]f32 =
    -- let m_elem = i32.i64 m
    let n_elem = i32.i64 n
    let A = flatten A
    let II1 = map (\i -> replicate n i) (iota m) |> flatten |> map i32.i64
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    in
    rankSearchBatchOptimized ks shp II1 A

-- Human Reasoning Version Optimized Test large inputs first iteration out
-- ==

-- entry: testRankSearchBatchOptimizedFstItOut

-- random input { [10000][100]f32 }
-- random input { [1000000][100]f32 }
-- random input { [10000][10000]f32 }
-- random input { [1000][100000]f32}
entry testRankSearchBatchOptimizedFstItOut [m] [n] (A : [m][n]f32) : [m]f32 =
    -- let m_elem = i32.i64 m
    let n_elem = i32.i64 n
    let A = flatten A
    let II1 = map (\i -> replicate n i) (iota m) |> flatten |> map i32.i64
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    in
    rankSearchBatchOptimizedFirstIterationOut ks shp II1 A


-- Radix Sort Version Test large inputs
-- ==

-- entry: testRadixSortRankSearchBatch

-- random input { [10000][100]f32 }
-- random input { [1000000][100]f32 }
-- random input { [10000][10000]f32 }
-- random input { [1000][100000]f32}
entry testRadixSortRankSearchBatch [m] [n] (A : [m][n]f32) : [m]f32 =
    let n_elem = i32.i64 n
    let A = flatten A
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    in radixSortRankSearchBatch ks shp A

-- Validation Unoptimized
-- ==
-- entry: validationUnoptimized
-- random input { [10000][100]f32 }
-- output { true }
-- random input { [1000000][100]f32 }
-- output { true }
-- random input { [10000][10000]f32 }
-- output { true }
-- random input { [1000][100000]f32}
-- output { true }
entry validationUnoptimized [m] [n] (A : [m][n]f32) : bool =
    let n_elem = i32.i64 n
    let A = flatten A
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    let II1 = map (\i -> replicate n i) (iota m) |> flatten |> map i32.i64

    let valid_res = radixSortRankSearchBatch ks shp A
    let test_res  = rankSearchBatchOptimized ks shp II1 A

    in reduce (&&) true (map2 (==) valid_res test_res)

-- Validation Optimized
-- ==
-- entry: validationOptimized
-- random input { [10000][100]f32 }
-- output { true }
-- random input { [1000000][100]f32 }
-- output { true }
-- random input { [10000][10000]f32 }
-- output { true }
-- random input { [1000][100000]f32}
-- output { true }
entry validationOptimized [m] [n] (A : [m][n]f32) : bool =
    let n_elem = i32.i64 n
    let A = flatten A
    let shp = replicate m n_elem
    let ks = replicate m (n_elem/2)
    let II1 = map (\i -> replicate n i) (iota m) |> flatten |> map i32.i64

    let valid_res = radixSortRankSearchBatch ks shp A
    let test_res  = rankSearchBatchOptimizedFirstIterationOut ks shp II1 A

    in reduce (&&) true (map2 (==) valid_res test_res)