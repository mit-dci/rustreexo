// Rustreexo

use super::types;
use super::util;

/// transform is the function used for re-organzing Utreexo tree. Given a vector
/// of positions to be deleted, it returns a
pub fn transform(mut dels: Vec<u64>, num_leaves: u64, forest_rows: u8) -> Vec<Vec<types::Arrow>> {
    let next_n_leaves = num_leaves - dels.len() as u64;

    let mut swaps: Vec<Vec<types::Arrow>> = Vec::with_capacity(forest_rows as usize);
    let mut collapses: Vec<Vec<types::Arrow>> = Vec::with_capacity(forest_rows as usize);

    for row in 0..forest_rows {
        let mut root_present = num_leaves&(1<<row) != 0;
        println!("Is root present: {}", root_present);
        let root_pos = util::root_position(num_leaves, row, forest_rows);

        // Does root exist. And is the last element in the root position
        if root_present && dels.last().unwrap() == &root_pos {
            dels.pop();

            // this is the same as running num_leaves&(1<<row) != 0; again
            // we know it's false
            root_present = false;
        }

        let del_remain = dels.len()%2 != 0;

        // Twin
        let mut twin_nextdels = util::extract_twins(dels.clone(), forest_rows);
        dels = twin_nextdels.1;

        swaps[row as usize] = make_swaps(dels.clone(), del_remain, root_present, root_pos);

        collapses[row as usize] = vec!(make_collapse(dels.clone(), del_remain, root_present, next_n_leaves, num_leaves, row, forest_rows).unwrap());

        let mut swap_nextdels = makeswap_nextdels(dels.clone(), del_remain, root_present, forest_rows);
twin_nextdels.0.append(&mut swap_nextdels);
        twin_nextdels.0.dedup();
        twin_nextdels.0.sort();

        dels = twin_nextdels.0;
    }

    swap_collapses(&mut swaps, &mut collapses, forest_rows);

    let collapse_iter = collapses.into_iter().enumerate();
    for collapse in collapse_iter {
        if collapse.0 == 1 && collapse.1[0].from != collapse.1[0].to {
            swaps[collapse.0 as usize].append(&mut vec!(collapse.1[0]));
        }
    }

    return swaps;
}

fn make_swaps(mut dels: Vec<u64>, del_remain: bool, root_present: bool, root_pos: u64) -> Vec<types::Arrow> {
    let n_swaps;
if del_remain && root_present {
        n_swaps = (dels.len() >> 1) + 1;
    } else {
        n_swaps = dels.len() >> 1;
    }

    let mut row_swaps: Vec<types::Arrow> = Vec::with_capacity(n_swaps);

    let mut i = 0;
    while dels.len() > 1 {
        row_swaps[i] = types::Arrow{from: dels[1] ^ 1, to: dels[0]};

        let to_keep = dels.len() - 2;
        dels.truncate(to_keep);
        i += 1;
    }

    // last swap
    if del_remain && root_present {
        row_swaps[i] = types::Arrow{from: root_pos, to: dels[0]}
    }

    return row_swaps;
}

fn make_collapse(mut dels: Vec<u64>, del_remain: bool, root_present: bool, next_n_leaves: u64, n_leaves: u64, row: u8, forest_rows: u8) -> Option<types::Arrow> {
    let root_dest = util::root_position(next_n_leaves, row, forest_rows);

    if !del_remain && root_present {
        let root_src = util::root_position(n_leaves, row, forest_rows);
        return Some(types::Arrow{from: root_src, to: root_dest});

    } else if del_remain && !root_present {
        let root_src = dels.pop().unwrap() ^ 1;
        return Some(types::Arrow{from: root_src, to: root_dest});

    } else {
        None
    }
}

fn makeswap_nextdels(mut dels: Vec<u64>, del_remain: bool, root_present: bool, forest_rows: u8) -> Vec<u64> {
    let n_swaps;

    if del_remain && root_present {
        n_swaps = (dels.len() >> 1) + 1;
    } else {
        n_swaps = dels.len() >> 1;
    }

    let mut swap_nextdels: Vec<u64> = Vec::with_capacity(n_swaps);

    let mut i = 0;
    while dels.len() > 1 {
        swap_nextdels[i] = util::parent(dels[1], forest_rows);

        let to_keep = dels.len() - 2;
        dels.truncate(to_keep);
        i += 1;
    }

    // last swap
    if del_remain && root_present {
        swap_nextdels[i] = util::parent(dels[0], forest_rows);
    }

    return swap_nextdels;
}

fn swap_collapses(swaps: &mut Vec<Vec<types::Arrow>>, collapses: &mut Vec<Vec<types::Arrow>>, forest_rows: u8) {
    if collapses.len() == 0 {
        return
    }

    let mut rows = collapses.len();

    // For all the collapses, go through all of them except for the root
    while rows != 0 {
        for swap in &swaps[rows] {
            swap_inrow(swap, collapses, rows as u8, forest_rows);
        }

        if collapses.len() == 0 {
            continue
        }

        let rowcol = collapses[rows][0].clone();
        swap_inrow(&rowcol, collapses, rows as u8, forest_rows);

        rows -= 1;
    }
}

fn swap_inrow(s: &types::Arrow, collapses: &mut Vec<Vec<types::Arrow>>, row: u8, forest_rows: u8) {
    let mut cr = 0;

    while cr < row {
        if collapses[cr as usize].len() == 0 {
            continue
        }

        let mask = swap_if_descendant(s, &collapses[cr as usize][0], row, cr, forest_rows);
        collapses[cr as usize][0].to ^= mask;

        cr += 1;
    }
}

fn swap_if_descendant(a: &types::Arrow, b: &types::Arrow, ar: u8, br: u8, forest_rows: u8) -> u64 {
    // ar=row of a, br=row of b, fr=forest_row
    let hdiff = ar - br;

    let b_up = util::n_grandparent(b.to, hdiff, forest_rows).unwrap();

    let mut sub_mask = 0;
    if (b_up == a.from) != (b_up == a.to) {
        let root_mask = a.from ^ a.to;
        sub_mask = root_mask << hdiff;
    }

    return sub_mask;

}
