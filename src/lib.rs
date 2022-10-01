//! A generic implimentation of a segment tree (or [range query tree](https://en.wikipedia.org/wiki/Range_query_tree)),
//! relying on a simple [`Merge`] trait to define the operation used during range queries. The zero-recursion approach is
//! taken from [this](https://www.geeksforgeeks.org/segment-tree-efficient-implementation/) excellent GeeksForGeeks article. 
//! 
// //! Example: (This example doesn't actually work because Rust won't let you impliment an external trait on an external type)
// //! ```
// //! use seg_tree::{SegTree, Merge};
// //! 
// //! impl Merge for i32 {
// //!    fn merge(l: &i32, r: &i32) -> i32 { *l + *r }
// //! }
// //! 
// //! fn main() {
// //!     let mut tree: SegTree = vec![1,2,-1,4].into();
// //!     assert_eq!(tree.query(0, 4), 6);
// //!     assert_eq!(tree.query(1, 3), 1);
// //!     tree.update(2, 3);
// //!     assert_eq!(tree.query(0, 4), 10);
// //!     assert_eq!(tree.query(1, 3), 5);
// //! }
// //! ```

/// A data structure for allowing both range queries and point updates on a sequence in `O(log(n))` time.
/// 
/// Internally, data is stored by allocating twice the memory required to hold the underlying sequence.
/// The sequence itself is then placed at the end ("bottom") of this range where each value represents a leaf node
/// in the tree, and parent nodes are populated "above" these leaf nodes such that the node at `segs[i]`
///   * can be said to have a "left child" (`left`) at `segs[2*i]` and a "right child" (`right`) at `segs[2*i+1]`.
///   * has a value equal to [`T::merge(left, right)`](Merge).
/// 
/// This is shown visually below for the sequence `[2,3,5,7]` and `T::merge` as `|l, r| l + r`:
/// ```norust
///            index (value)
/// +-------------------------------+
/// |            1 (17)             |
/// +---------------+---------------+
/// |     2 (5)     |    3 (12)     |
/// +-------+-------+-------+-------+
/// | 4 (2) | 5 (3) | 6 (5) | 4 (7) |
/// +-------+-------+-------+-------+
/// ```
pub struct SegTree<T> {
    segs: Vec<T>,
    n: usize
}

/// A trait for defining the operation that should be used when accumulating values in a range query.
/// Although not required by the type system, this operation _should_ be associative for the results
/// of [`SegTree::query`] to make any sense.
pub trait Merge {
    fn merge(l: &Self, r: &Self) -> Self;
}


impl<T> From<Vec<T>> for SegTree<T> 
where T: Merge + Default + Clone // Default and Clone aren't strictly needed here, but I'm too lazy to deal with MaybeUninit
{
    fn from(items: Vec<T>) -> Self {
        // Initialize a block of memory big enough to hold twice the total leaf nodes (guaranteed to be enough space for a binary tree)
        let n = items.len();
        let mut tree = SegTree {
            segs: vec![T::default(); items.len()*2],
            n, 
        };

        // Copy the leaf nodes onto the end of the block
        for (i, x) in items.into_iter().enumerate() {
            tree.segs[n+i] = x;
        }

        // Work our way back from the start of the leaf nodes, populating parent nodes as we go
        for i in (0..n).rev() {
            tree.segs[i] = T::merge(&tree.segs[2*i], &tree.segs[2*i+1]);
        }

        tree
    }
}

impl<T> SegTree<T> {
    /// Quickly compute the result of accumulating all elements from `l` (inclusive) to `r` (exclusive), via [`T::merge`](Merge).
    pub fn query(&self, l: usize, r: usize) -> T where T: Merge + Default
    {
        let mut l = self.n + l;
        let mut r = self.n + r; 
        let mut res = T::default(); 

        while l != r {
            // If `l` is a right child, we want to count it but not its parent. Left-merge its value with `res`, then step right so that
            // when `l` next steps up the tree, we're visiting its right neighbor's parent, not its original parent.
            if l % 2 == 1 {
                res = T::merge(&self.segs[l], &res);
                l += 1;
            }

            // If `r` is a right child, we want to count only its left sibling (because the `r` bound is exclusive). Step left, then 
            // right-merge that value with `res`. Note that we never have to worry double-counting when visiting `r`'s parent in the 
            // next iteration; If `r`'s parent is a left child then we'll ignore it, and if it is a right child then we'll end up counting 
            // `r`'s left uncle instead of `r`'s parent.
            if r % 2 == 1 {
                r -= 1;
                res = T::merge(&res, &self.segs[r]);
            }

            // Step `l` and `r` up the tree to their respective parent nodes.
            l /= 2;
            r /= 2;
        }

        res
    }

    /// Update the value at a certain index in the sequence underlying this `SegTree` and recompute everything needed to continue
    /// rapid queries with [`SegTree::query`].
    pub fn update(&mut self, i: usize, val: T) where T: Merge{
        let mut i = self.n + i;
        self.segs[i] = val;
        
        while i > 1 {
            i /= 2;
            self.segs[i] = T::merge(&self.segs[2*i], &self.segs[2*i+1]);
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use rand::{self, Rng};

    impl Merge for i32 {
        fn merge(l: &Self, r: &Self) -> Self {
            l + r
        }
    }

    fn naive_query<T>(seq: &[T], l: usize, r: usize) -> T 
    where T: Merge + Default
    {
        let mut res = T::default();
        for i in l..r {
            res = T::merge(&res, &seq[i])
        }
        res
    }

    #[test]
    fn query_1() {
        let tree: SegTree<_> = vec![1,2,3,4].into();
        assert_eq!(tree.query(0, 4), 10);
        assert_eq!(tree.query(1, 3), 5);
    }

    #[test]
    fn query_2() {
        let tree: SegTree<_> = vec![1,2,3].into();
        assert_eq!(tree.query(0, 3), 6);
        assert_eq!(tree.query(0, 2), 3);
    }

    #[test]
    fn query_many() {
        let min_n = 10;
        let max_n = 100;
        let test_queries = 10;
        let tests = 100;

        let mut rng = rand::thread_rng();

        for _ in 0..tests {
            let n = rng.gen_range(min_n..max_n+1);
            let mut vals = Vec::with_capacity(n);
            for _ in 0..n {
                vals.push( rng.gen_range(-100..100) )
            }

            let tree: SegTree<_> = vals.into();
            for _ in 0..test_queries {
                let l = rng.gen_range(0..n-1);
                let r = rng.gen_range(l+1..n);
                assert_eq!(
                    naive_query(&tree.segs[n..], l, r),
                    tree.query(l, r)
                )
            }
        }
    }


    #[test]
    fn update_1() {
        let mut tree: SegTree<_> = vec![1,2,3,4].into();
        tree.update(2, 9);
        assert_eq!(tree.query(0, 4), 16);
        assert_eq!(tree.query(1, 3), 11);
    }

    #[test]
    fn update_2() {
        let mut tree: SegTree<_> = vec![1,2,3].into();
        tree.update(1, -1);
        assert_eq!(tree.query(0, 3), 3);
        assert_eq!(tree.query(0, 2), 0);
    }

    #[test]
    fn update_many() {
        let min_n = 10;
        let max_n = 100;
        let test_queries = 10;
        let tests = 100;

        let mut rng = rand::thread_rng();

        for _ in 0..tests {
            let n = rng.gen_range(min_n..max_n+1);
            let mut vals = Vec::with_capacity(n);
            for _ in 0..n {
                vals.push( rng.gen_range(-100..100) )
            }

            let mut tree: SegTree<_> = vals.into();
            for _ in 0..test_queries {
                let i = rng.gen_range(0..n);
                tree.update(i, rng.gen_range(-100..100) );

                let l = rng.gen_range(0..n-1);
                let r = rng.gen_range(l+1..n);
                assert_eq!(
                    naive_query(&tree.segs[n..], l, r),
                    tree.query(l, r)
                )
            }
        }
    }
}
