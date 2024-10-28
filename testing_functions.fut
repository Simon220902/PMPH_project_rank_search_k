let partition3 [n] 't
        (p1 : (t -> bool))
        (p2 : (t -> bool))
        (arr : [n]t) : ([n]t, (i64, i64)) = 
    -- If we just call the second predicate on the array first and then the first predicate we will get:
    -- p1 : (\ (a, b) -> a == 1) 
    -- p2 : (\ (a, b) -> b == 1) 
    -- arr : [(0,0), (1,0), (0, 1), (0,0), (0,1), (1,0)]
    -- partition3 p1 p2 arr => [(1, 0), (1,0), (0, 1), (0, 1), (0,0), (0,0)]

    -- [p1 | p2 | neither]


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

let partition3new [n] 't
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
    --(arr_partioned, (cnt_lth, cnt_eq))
    let inds = map5 (\ c1 c2 iT1 iT2 iF ->
                        if c1 then iT1-1
                        else if c2 then iT2-1
                        else iF - 1
                     ) cs1 cs2 isT1 isT2 isF

    let arr' = scatter (copy arr) inds arr
    in
    (arr', (i1, i2))

let testnew =
    let arr = [9, 3, 4, 5,2,1,3,57,5,25,2,4]
    let p = arr[(length arr) - 1]
    in (partition3 (< p) (== p) arr) == (partition3new (< p) (== p) arr)