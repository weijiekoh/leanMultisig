use multilinear_toolkit::prelude::*;
use tracing::instrument;

#[instrument(skip_all)]
pub fn matrix_up_folded<F: ExtensionField<PF<F>>>(outer_challenges: &[F], alpha: F) -> Vec<F> {
    let n = outer_challenges.len();
    let mut folded = eval_eq_scaled(outer_challenges, alpha);
    let outer_challenges_prod: F = outer_challenges.iter().copied().product();
    folded[(1 << n) - 1] -= outer_challenges_prod * alpha;
    folded[(1 << n) - 2] += outer_challenges_prod * alpha;
    folded
}

#[instrument(skip_all)]
pub fn matrix_down_folded<F: ExtensionField<PF<F>>>(outer_challenges: &[F], dest: &mut [F]) {
    let n = outer_challenges.len();
    for k in 0..n {
        let outer_challenges_prod = (F::ONE - outer_challenges[n - k - 1])
            * outer_challenges[n - k..].iter().copied().product::<F>();
        let mut eq_mle = eval_eq_scaled(&outer_challenges[0..n - k - 1], outer_challenges_prod);
        for (mut i, v) in eq_mle.iter_mut().enumerate() {
            i <<= k + 1;
            i += 1 << k;
            dest[i] += *v;
        }
    }
    // bottom left corner:
    dest[(1 << n) - 1] += outer_challenges.iter().copied().product::<F>();
}
