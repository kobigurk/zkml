pub mod helpers;
pub mod loader;
pub mod proving_ipa;
pub mod proving_kzg;

pub fn div_ceil(a: usize, b: usize) -> usize {
  (a + b - 1) / b
}