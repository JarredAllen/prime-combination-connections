//! List the size of the various connected components around `00001` for various radices.
//!
//! I was curious how it would interact, as a larger radix means we get more options to try, but
//! also means those options will be larger (and therefore, less likely to be prime).
//!
//! The results that I got (only going up to base 36) are pretty complicated. I need to optimize it
//! better before I try anything larger.
//!
//! Here's the values I computed for this range:
//! ```text
#![doc = include_str!("./max_connected_size.out")]
//! ```

use prime_combination_connections::Number;

/// Print the absolute count and relative fraction for the values reachable from `00001` in a given
/// number base.
macro_rules! for_n {
    ($n:literal) => {{
        let component_size = Number::<5, $n>::from(1).connected_component().len();
        println!(
            concat!(stringify!($n), ": {} ({:.2}%)"),
            component_size,
            100. * component_size as f32 / ($n as usize).pow(5) as f32,
        );
    }};
}

fn main() {
    for_n!(2);
    for_n!(3);
    for_n!(4);
    for_n!(5);
    for_n!(6);
    for_n!(7);
    for_n!(8);
    for_n!(9);
    for_n!(10);
    for_n!(11);
    for_n!(12);
    for_n!(13);
    for_n!(14);
    for_n!(15);
    for_n!(16);
    for_n!(17);
    for_n!(18);
    for_n!(19);
    for_n!(20);
    for_n!(21);
    for_n!(22);
    for_n!(23);
    for_n!(24);
    for_n!(25);
    for_n!(26);
    for_n!(27);
    for_n!(28);
    for_n!(29);
    for_n!(30);
    for_n!(31);
    for_n!(32);
    for_n!(33);
    for_n!(34);
    for_n!(35);
    for_n!(36);
}
