# Overview
A generic implimentation of a segment tree (or [range query tree](https://en.wikipedia.org/wiki/Range_query_tree)) in Rust,
relying on a simple `Merge` trait to define the operation used during range queries. The zero-recursion approach is
taken from [this](https://www.geeksforgeeks.org/segment-tree-efficient-implementation/) excellent GeeksForGeeks article.
