import "lib/github.com/diku-dk/sorts/radix_sort"

-- Radix sort based Rank search K
-- ==
-- entry: radix_sort_based_rank_search_k
-- input {4i64 [1f32, 2f32, 3f32, 4f32, 5f32, 6f32, 7f32, 8f32, 9f32, 10f32, 11f32, 12f32]}
-- output { 4f32 }
-- random input { 50000i64 [100000]f32 }
-- random input { 500000i64 [1000000]f32 }
entry radix_sort_based_rank_search_k (k: i64) (A: []f32) : f32 =
  let sorted_array = radix_sort f32.num_bits f32.get_bit A in
  sorted_array[k-1]

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


