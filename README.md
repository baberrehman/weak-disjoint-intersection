# weak-disjoint-intersection

The purpose of weak disjoint intersection types is to support function overloading in disjoint intersection types.
Disjoint intersection types restrict the merges like ```((Int -> Int) ,, (String -> Int))```. Our goal is to
allow merging two functions if either input types or the output types are not overlapping.