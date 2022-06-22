// Rustreexo

use std::vec::Vec;
// isRootPosition checks if the current position is a root given the number of
// leaves and the entire rows of the forest.
pub fn is_root_position(position: u64, num_leaves: u64, forest_rows: u8) -> bool {
    let row = detect_row(position, forest_rows);

    let root_present = num_leaves & (1 << row) != 0;
    let root_pos = root_position(num_leaves, row, forest_rows);

    return root_present && root_pos == position;
}

// extractTwins is a optimization for batched deletions. It checks if the nodes
// being deleted also have their sibling being deleted. It returns the parents
// of the deleted siblings along with nodes that didn't have a sibling
pub fn extract_twins(nodes: Vec<u64>, forest_rows: u8) -> (Vec<u64>, Vec<u64>) {
    let mut parents = Vec::new();
    let mut twined = Vec::new();

    // iterate and check if the next element is its sibling
    let node_iter = nodes.windows(2);

    for n in node_iter {
        // If the next node in line is the current node's sibling
        // grab the parent as well
        if n[0] | 1 == n[1] {
            parents.push(parent(n[0], forest_rows));
            twined.push(n[0]);
            twined.push(n[1]);
        }
    }

    return (parents, twined);
}
pub fn is_left_niece(position: u64) -> bool {
    position & 1 == 0
}
// detectSubTreeHight finds the rows of the subtree a given LEAF position and
// the number of leaves (& the forest rows which is redundant)
// Go left to right through the bits of numLeaves,
// and subtract that from position until it goes negative.
// (Does not work for nodes that are not at the bottom)
pub fn detect_sub_tree_rows(pos: u64, num_leaves: u64, forest_rows: u8) -> u8 {
    let mut h = forest_rows;
    let mut marker = pos;

    while marker >= (1 << h) & num_leaves {
        marker -= (1 << h) & num_leaves;
        h -= 1;
    }

    return h;
}

pub fn detect_row_hashes(
    targets: &Vec<u64>,
    target_row: u8,
    forest_rows: u8,
) -> Result<(u64, u64), String> {
    let mut start: i64 = -1;
    let mut end: i64 = -1;

    for i in 0..targets.len() {
        if detect_row(targets[i], forest_rows) == target_row as u8 {
            if start == -1 {
                start = i as i64;
            }
            end = i as i64;
        } else {
            if start != -1 {
                break;
            }
        }
    }

    if start == -1 || end == -1 {
        return Err(String::from("Row not found!"));
    }

    Ok((start as u64, end as u64))
}
pub fn num_roots(leafs: u64) -> usize {
    leafs.count_ones() as usize
}

// detectRow finds the current row of a node, given the position
// and the total forest rows.
pub fn detect_row(pos: u64, forest_rows: u8) -> u8 {
    let mut marker: u64 = 1 << forest_rows;
    let mut h: u8 = 0;

    while pos & marker != 0 {
        marker >>= 1;
        h += 1;
    }

    return h;
}

pub fn detect_offset(pos: u64, num_leaves: u64) -> (u8, u8, u64) {
    let mut tr = tree_rows(num_leaves);
    let nr = detect_row(pos, tr);

    let mut bigger_trees: u8 = 0;
    let mut marker = pos;

    // add trees until you would exceed position of node

    // This is a bit of an ugly predicate.  The goal is to detect if we've
    // gone past the node we're looking for by inspecting progressively shorter
    // trees; once we have, the loop is over.

    // The predicate breaks down into 3 main terms:
    // A: pos << nh
    // B: mask
    // C: 1<<th & num_leaves (tree_size)
    // The predicate is then if (A&B >= C)
    // A is position up-shifted by the row of the node we're targeting.
    // B is the "mask" we use in other functions; a bunch of 0s at the MSB side
    // and then a bunch of 1s on the LSB side, such that we can use bitwise AND
    // to discard high bits.  Together, A&B is shifting position up by nr bits,
    // and then discarding (zeroing out) the high bits.  This is the same as in
    // n_grandchild.  C checks for whether a tree exists at the current tree
    // rows.  If there is no tree at tr, C is 0.  If there is a tree, it will
    // return a power of 2: the base size of that tree.
    // The C term actually is used 3 times here, which is ugly; it's redefined
    // right on the next line.
    // In total, what this loop does is to take a node position, and
    // see if it's in the next largest tree.  If not, then subtract everything
    // covered by that tree from the position, and proceed to the next tree,
    // skipping trees that don't exist.

    while (marker << nr) & ((2 << tr) - 1) >= (1 << tr) & num_leaves {
        let tree_size = (1 << tr) & num_leaves;
        if tree_size != 0 {
            marker -= tree_size;
            bigger_trees += 1;
        }
        tr -= 1;
    }

    return (bigger_trees, tr - nr, !marker);
}

// parent returns the parent position of the passed in child
pub fn parent(pos: u64, forest_rows: u8) -> u64 {
    (pos >> 1) | (1 << forest_rows)
}

// n_grandparent returns the parent postion of the passed in child
// the generations to go will be determined by rise
// ex: rise = 3 will return a great-grandparent
pub fn n_grandparent(pos: u64, rise: u8, forest_rows: u8) -> Result<u64, u8> {
    if rise == 0 {
        return Ok(pos);
    }
    if rise > forest_rows {
        return Err(1);
    }
    let mask = (2 << forest_rows) - 1;
    Ok((pos >> rise | (mask << (forest_rows - (rise - 1)))) & mask)
}

pub fn in_forest(mut pos: u64, num_leaves: u64, forest_rows: u8) -> bool {
    // quick yes
    if pos < num_leaves {
        return true;
    }

    let marker = 1 << forest_rows;
    let mask = (marker << 1) - 1;

    if pos >= mask {
        return false;
    }

    while pos & marker != 0 {
        pos = ((pos << 1) & mask) | 1;
    }

    return pos < num_leaves;
}

// tree_rows returns the number of rows given n leaves
pub fn tree_rows(n: u64) -> u8 {
    // tree_rows works by:
    // 1. Find the next power of 2 from the given n leaves.
    // 2. Calculate the log2 of the result from step 1.
    //
    // For example, if the given number is 9, the next power of 2 is
    // 16. This log2 of this number is how many rows there are in the
    // given tree.
    //
    // This works because while Utreexo is a collection of perfect
    // trees, the allocated number of leaves is always a power of 2.
    // For Utreexo trees that don't have leaves that are power of 2,
    // the extra space is just unallocated/filled with zeros.

    let t = next_pow2(n);

    // log of 2 is the tree depth/height
    // if n == 0, there will be 64 trailing zeros but actually no tree rows
    // we clear the 6th bit to return 0 in that case.
    (t.trailing_zeros() & !64) as u8
}

// root_position returns the position of the root at a given row
// TODO undefined behavior if the given row doesn't have a root
pub fn root_position(num_leaves: u64, row: u8, forest_rows: u8) -> u64 {
    let mask = (2 << forest_rows) - 1;
    let before = num_leaves & (mask << (row + 1));

    let shifted = (before >> row) | (mask << (forest_rows + 1 - row));
    shifted & mask
}

/// Returns whether next is node's sibling or not
pub fn is_right_sibling(node: u64, next: u64) -> bool {
    node | 1 == next
}

// get_roots_reverse gives you the positions of the tree roots, given a number of leaves.

// next_pow2 returns the next power of 2
// ex: n = 9 will return 16. n = 33 will return 64
fn next_pow2(n: u64) -> u64 {
    let mut t = n - 1;
    t |= t >> 1;
    t |= t >> 2;
    t |= t >> 4;
    t |= t >> 8;
    t |= t >> 16;
    t |= t >> 32;
    t + 1
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_root_position() {
        let pos = super::root_position(5, 2, 3);
        assert_eq!(pos, 12);

        let pos = super::root_position(5, 0, 3);
        assert_eq!(pos, 4);
    }
    #[test]
    fn test_is_right_sibling() {
        assert!(super::is_right_sibling(0, 1));
    }
    #[test]
    fn pow_tests() {
        // Check one
        assert_eq!(super::next_pow2(1), 1);

        // Check 2 through 64
        for i in 2..64u64 {
            let x = 1 << i - 1;
            assert_eq!(super::next_pow2(x), 1 << (i - 1));
        }
    }

    #[test]
    fn util_test() {
        let test = vec![0, 1, 2, 3, 4, 7, 10];

        let x = super::extract_twins(test, 4);
        assert_eq!(x.1, vec![0, 1, 2, 3]);

        for leaf_count in 4..1000 {
            for pos in 0..leaf_count {
                let n_vec = vec![pos, pos | 1, pos + 2, pos + 10];
                let x = super::extract_twins(n_vec, super::tree_rows(leaf_count));
                assert_eq!(x.1, vec![pos, pos | 1]);
            }
        }
    }
    fn row_offset(row: u8, forest_rows: u8) -> u64 {
        // 2 << forestRows is 2 more than the max poisition
        // to get the correct offset for a given row,
        // subtract (2 << `row complement of forestRows`) from (2 << forestRows)
        (2 << forest_rows) - (2 << (forest_rows - row))
    }
    #[test]
    fn test_detect_row() {
        for forest_rows in 1..63 {
            // Test top
            let top_pos = (2 << forest_rows) - 2;
            let row_result = super::detect_row(top_pos, forest_rows);

            assert_eq!(row_result, forest_rows);

            // Test others
            for row in 0..forest_rows {
                let pos = row_offset(row, forest_rows);
                let row_result = super::detect_row(pos, forest_rows);

                assert_eq!(row, row_result);
            }
        }
    }
    #[test]
    fn test_is_root_position() {
        let h = super::is_root_position(14, 8, 3);
        assert_eq!(h, true);
    }
    #[test]
    fn test_detect_subtree_rows() {
        let h = super::detect_sub_tree_rows(0, 8, 3);
        assert_eq!(h, 3);
    }
}
