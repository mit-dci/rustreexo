use std::io::Read;

// Rustreexo
use super::node_hash::NodeHash;

// isRootPosition checks if the current position is a root given the number of
// leaves and the entire rows of the forest.
pub fn is_root_position(position: u64, num_leaves: u64, forest_rows: u8) -> bool {
    let row = detect_row(position, forest_rows);

    let root_present = num_leaves & (1 << row) != 0;
    let root_pos = root_position(num_leaves, row, forest_rows);

    root_present && root_pos == position
}

// removeBit removes the nth bit from the val passed in. For example, if the 2nd
// bit is to be removed from 1011 (11 in dec), the returned value is 111 (7 in dec).
pub fn remove_bit(val: u64, bit: u64) -> u64 {
    let mask = ((2 << bit) - 1) as u64;
    let upper_mask = std::u64::MAX ^ mask;
    let upper = val & upper_mask;

    let mask = ((1 << bit) - 1) as u64;
    let lower_mask = !(std::u64::MAX ^ mask);
    let lower = val & lower_mask;

    (upper >> 1) | lower
}
pub fn calc_next_pos(position: u64, del_pos: u64, forest_rows: u8) -> Result<u64, String> {
    let del_row = detect_row(del_pos, forest_rows);
    let pos_row = detect_row(position, forest_rows);

    if del_row < pos_row {
        return Err(format!(
            "calc_next_pos fail: del_pos of {} is at a lower row than position at {}",
            del_pos, position
        ));
    }

    // This is the lower bits where we'll remove the nth bit.
    let lower_bits = remove_bit(position, (del_row - pos_row) as u64);

    // This is the bit to be prepended.
    let to_row = pos_row + 1;
    let higher_bits = (1 << to_row) << (forest_rows - to_row) as u64;

    // Put the bits together and return it.
    Ok(higher_bits | lower_bits)
}
pub fn detwin(nodes: Vec<u64>, forest_rows: u8) -> Vec<u64> {
    let mut dels_after = nodes;
    let mut n = 0;

    while (n + 1) < dels_after.len() {
        // If the next node in line is the current node's sibling
        // grab the parent as well
        let i = dels_after[n];
        let j = dels_after[n + 1];

        if is_right_sibling(i, j) {
            dels_after.drain(n..n + 2);
            dels_after = add_and_sort(dels_after, parent(i, forest_rows));
        } else {
            n += 1;
        }
    }

    dels_after
}
// start_position_at_row returns the smallest position an accumulator can have for the
// requested row for the given numLeaves.
pub fn start_position_at_row(row: u8, forest_rows: u8) -> u64 {
    // 2 << forest_rows is 2 more than the max position
    // to get the correct offset for a given row,
    // subtract (2 << `row complement of forest_rows`) from (2 << forest_rows)
    (2 << forest_rows) - (2 << (forest_rows - row)) as u64
}
fn add_and_sort(mut vec: Vec<u64>, value: u64) -> Vec<u64> {
    vec.push(value);
    vec.sort();
    vec
}
pub fn is_left_niece(position: u64) -> bool {
    position & 1 == 0
}
pub fn left_sibling(position: u64) -> u64 {
    (position | 1) ^ 1
}
// roots_to_destroy returns the empty roots that get written over after num_adds
// amount of leaves have been added.
pub fn roots_to_destroy(num_adds: u64, mut num_leaves: u64, orig_roots: &[NodeHash]) -> Vec<u64> {
    let mut roots = orig_roots.to_vec();
    let mut deleted = vec![];
    let mut h = 0;
    for add in 0..num_adds {
        while (num_leaves >> h) & 1 == 1 {
            let root = roots
                .pop()
                .expect("If (num_leaves >> h) & 1 == 1, it must have at least one root left");
            if root.is_empty() {
                let root_pos =
                    root_position(num_leaves, h, tree_rows(num_leaves + (num_adds - add)));
                deleted.push(root_pos);
            }
            h += 1;
        }
        // Just adding a non-zero value to the slice.
        roots.push(NodeHash::placeholder());
        num_leaves += 1;
    }

    deleted
}

pub fn num_roots(leaves: u64) -> usize {
    leaves.count_ones() as usize
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

    h
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

    (bigger_trees, tr - nr, !marker)
}

pub fn children(pos: u64, forest_rows: u8) -> u64 {
    let mask = (2 << forest_rows) - 1;
    (pos << 1) & mask
}
pub fn left_child(pos: u64, forest_rows: u8) -> u64 {
    children(pos, forest_rows)
}
pub fn right_child(pos: u64, forest_rows: u8) -> u64 {
    children(pos, forest_rows) + 1
}

pub fn is_root_populated(row: u8, num_leaves: u64) -> bool {
    (num_leaves >> row) & 1 == 1
}
/// max_position_at_row returns the biggest position an accumulator can have for the
/// requested row for the given num_leaves.
pub fn max_position_at_row(row: u8, total_rows: u8, num_leaves: u64) -> Result<u64, String> {
    Ok(parent_many(num_leaves, row, total_rows)?.saturating_sub(1))
}
// parent returns the parent position of the passed in child
pub fn parent(pos: u64, forest_rows: u8) -> u64 {
    (pos >> 1) | (1 << forest_rows)
}
pub fn read_u64<Source: Read>(buf: &mut Source) -> Result<u64, String> {
    let mut bytes = [0u8; 8];
    buf.read_exact(&mut bytes)
        .map_err(|_| "Failed to read u64")?;
    Ok(u64::from_le_bytes(bytes))
}
// tree_rows returns the number of rows given n leaves
pub fn tree_rows(n: u64) -> u8 {
    if n == 0 {
        return 0;
    }
    // 64 is the number of bits in an u64. We can't use use u64::BITS, because this
    // was added on 1.53, and our MSRV is 1.41
    (64 - (n - 1).leading_zeros()) as u8
}

// root_position returns the position of the root at a given row
// TODO undefined behavior if the given row doesn't have a root
pub fn root_position(num_leaves: u64, row: u8, forest_rows: u8) -> u64 {
    let mask = (2 << forest_rows) - 1;
    let before = num_leaves & (mask << (row + 1));

    let shifted = (before >> row) | (mask << (forest_rows + 1 - row));
    shifted & mask
}
pub fn parent_many(pos: u64, rise: u8, forest_rows: u8) -> Result<u64, String> {
    if rise == 0 {
        return Ok(pos);
    }
    if rise > forest_rows {
        return Err(format!(
            "Cannot rise more than the forestRows: rise: {} forest_rows: {}",
            rise, forest_rows
        ));
    }
    let mask = ((2 << forest_rows) - 1) as u64;
    Ok((pos >> rise | (mask << (forest_rows - (rise - 1)) as u64)) & mask)
}

pub fn is_ancestor(higher_pos: u64, lower_pos: u64, forest_rows: u8) -> Result<bool, String> {
    if higher_pos == lower_pos {
        return Ok(false);
    }
    let lower_row = detect_row(lower_pos, forest_rows);
    let higher_row = detect_row(higher_pos, forest_rows);

    // Prevent underflows by checking that the higherRow is not less
    // than the lowerRow.
    if higher_row < lower_row {
        return Ok(false);
    }
    // Return false if we error out or the calculated ancestor doesn't
    // match the higherPos.
    let ancestor = parent_many(lower_pos, higher_row - lower_row, forest_rows)?;

    Ok(higher_pos == ancestor)
}

/// Returns whether next is node's sibling or not
pub fn is_right_sibling(node: u64, next: u64) -> bool {
    node | 1 == next
}

/// Returns whether a and b are sibling or not
fn is_sibling(a: u64, b: u64) -> bool {
    a ^ 1 == b
}
/// Returns which node should have its hashes on the proof, along with all nodes
/// whose hashes will be calculated to reach a root
pub fn get_proof_positions(targets: &[u64], num_leaves: u64, forest_rows: u8) -> Vec<u64> {
    let mut proof_positions = vec![];
    let mut computed_positions = targets.to_vec();
    computed_positions.sort();

    for row in 0..=forest_rows {
        let mut row_targets = computed_positions
            .iter()
            .copied()
            .filter(|x| super::util::detect_row(*x, forest_rows) == row)
            .collect::<Vec<_>>()
            .into_iter()
            .peekable();

        while let Some(node) = row_targets.next() {
            if is_root_position(node, num_leaves, forest_rows) {
                let idx = computed_positions.iter().position(|x| node == *x).unwrap();

                computed_positions.remove(idx);
                continue;
            }
            if let Some(next) = row_targets.peek() {
                if !is_sibling(node, *next) {
                    proof_positions.push(node ^ 1);
                } else {
                    row_targets.next();
                }
            } else {
                proof_positions.push(node ^ 1);
            }

            computed_positions.push(parent(node, forest_rows));
            computed_positions.sort();
        }
    }

    proof_positions
}
#[cfg(any(test, bench))]
pub fn hash_from_u8(value: u8) -> NodeHash {
    use bitcoin_hashes::sha256;
    use bitcoin_hashes::Hash;
    use bitcoin_hashes::HashEngine;
    let mut engine = bitcoin_hashes::sha256::Hash::engine();

    engine.input(&[value]);

    sha256::Hash::from_engine(engine).into()
}
#[cfg(test)]
mod tests {
    use std::str::FromStr;
    use std::vec;

    use super::roots_to_destroy;
    use crate::accumulator::node_hash::NodeHash;
    use crate::accumulator::util::children;
    use crate::accumulator::util::tree_rows;

    #[test]
    fn test_proof_pos() {
        let unsorted = vec![33, 35, 32, 34, 50, 52];
        let sorted = vec![33, 35, 32, 34, 50, 52];
        let num_leaves = 32_u64;
        let num_rows = tree_rows(num_leaves);

        // Test that un-sorted targets results in the same result as the sorted vec.
        assert_eq!(
            super::get_proof_positions(&unsorted, num_leaves, num_rows),
            super::get_proof_positions(&sorted, num_leaves, num_rows)
        );
    }
    #[test]
    fn test_is_sibling() {
        assert!(super::is_sibling(0, 1));
        assert!(super::is_sibling(1, 0));
        assert!(!super::is_sibling(1, 2));
        assert!(!super::is_sibling(2, 1));
    }
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
    fn test_roots_to_destroy() {
        let roots = ["0000000000000000000000000000000000000000000000000000000000000000",
            "aad41f1d55e1a111ca193f6fa4e13dfc0cbdfbea851b30f3eacfe8d9d6be4302",
            "0000000000000000000000000000000000000000000000000000000000000000",
            "3c2d8cbe4336bbe05fff898102d413ab6356de2598aad4d5a7f916c5b316cb42"];
        let roots = roots
            .iter()
            .map(|hash| NodeHash::from_str(hash).unwrap())
            .collect::<Vec<_>>();

        let deleted = roots_to_destroy(1, 15, &roots);

        assert_eq!(deleted, vec![22, 28])
    }
    #[test]
    fn test_remove_bit() {
        // This should remove just one bit from the final number
        // 15 = 1111, removing bit 3 makes it 111, that is 7
        let res = super::remove_bit(11, 2);
        assert_eq!(res, 7);
        // 1010 => 101
        let res = super::remove_bit(10, 0);
        assert_eq!(res, 5);

        // 1110 => 110
        let res = super::remove_bit(14, 1);
        assert_eq!(res, 6);
    }
    #[test]
    fn test_detwin() {
        // 14
        // |---------------\
        // 12              13
        // |-------\       |-------\
        // 08      09      10      11
        // |---\   |---\   |---\   |---\
        // 00  01  02  03  04  05  06  07
        let targets: Vec<u64> = vec![0, 1, 4, 5, 7];
        let targets = super::detwin(targets, 3);
        assert_eq!(targets, vec![7, 8, 10]);

        let targets = vec![4, 6, 8, 9];
        let targets = super::detwin(targets, 3);
        assert_eq!(targets, vec![4, 6, 12]);
    }

    #[test]
    fn test_tree_rows() {
        assert_eq!(super::tree_rows(8), 3);
        assert_eq!(super::tree_rows(9), 4);
        assert_eq!(super::tree_rows(12), 4);
        assert_eq!(super::tree_rows(255), 8);
    }
    fn row_offset(row: u8, forest_rows: u8) -> u64 {
        // 2 << forestRows is 2 more than the max position
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

    fn test_get_proof_positions() {
        let targets: Vec<u64> = vec![4, 5, 7, 8];
        let num_leaves = 8;
        let targets =
            super::get_proof_positions(&targets, num_leaves, super::tree_rows(num_leaves));

        assert_eq!(vec![6, 9], targets);
    }
    #[test]
    fn test_is_root_position() {
        let h = super::is_root_position(14, 8, 3);
        assert!(h);
    }
    #[test]
    fn test_children_pos() {
        assert_eq!(children(4, 2), 0);
        assert_eq!(children(49, 5), 34);
        assert_eq!(children(50, 5), 36);
        assert_eq!(children(44, 5), 24);
    }
    #[test]
    fn test_calc_next_pos() {
        let res = super::calc_next_pos(0, 1, 3);
        assert_eq!(Ok(8), res);

        let res = super::calc_next_pos(1, 9, 3);
        assert_eq!(Ok(9), res);
    }
}
