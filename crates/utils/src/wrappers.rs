use p3_challenger::DuplexChallenger;
use p3_field::BasedVectorSpace;
use p3_field::ExtensionField;
use p3_field::PackedFieldExtension;
use p3_field::PackedValue;
use p3_field::PrimeField64;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_koala_bear::KoalaBear;
use p3_symmetric::CryptographicHasher;
use p3_symmetric::PaddingFreeSponge;
use p3_symmetric::PseudoCompressionFunction;
use p3_symmetric::TruncatedPermutation;

use rayon::prelude::*;
use whir_p3::fiat_shamir::{prover::ProverState, verifier::VerifierState};
use whir_p3::whir::committer::Witness;
use whir_p3::whir::committer::reader::ParsedCommitment;
use whir_p3::whir::config::WhirConfigBuilder;

use crate::Poseidon16;
use crate::Poseidon24;
use crate::get_poseidon16;
use crate::get_poseidon24;

pub type PF<F> = <F as PrimeCharacteristicRing>::PrimeSubfield;
pub type PFPacking<F> = <PF<F> as Field>::Packing;
pub type EFPacking<EF> = <EF as ExtensionField<PF<EF>>>::ExtensionPacking;

pub type FSProver<EF, Challenger> = ProverState<PF<EF>, EF, Challenger>;
pub type FSVerifier<EF, Challenger> = VerifierState<PF<EF>, EF, Challenger>;

pub type MyMerkleHash = PaddingFreeSponge<Poseidon24, 24, 16, 8>; // leaf hashing
pub type MyMerkleCompress = TruncatedPermutation<Poseidon16, 2, 8, 16>; // 2-to-1 compression
pub type MyChallenger = DuplexChallenger<KoalaBear, Poseidon16, 16, 8>;
pub type MyWhirConfigBuilder = WhirConfigBuilder<MyMerkleHash, MyMerkleCompress, MY_DIGEST_ELEMS>;
pub type WhirWitness<F, EF> = Witness<F, EF, MY_DIGEST_ELEMS>;
pub type WhirParsedCommitment<F, EF> = ParsedCommitment<F, EF, MY_DIGEST_ELEMS>;
pub const MY_DIGEST_ELEMS: usize = 8;

pub fn build_challenger() -> MyChallenger {
    MyChallenger::new(get_poseidon16().clone())
}

pub fn build_merkle_hash() -> MyMerkleHash {
    MyMerkleHash::new(get_poseidon24().clone())
}

pub fn build_merkle_compress() -> MyMerkleCompress {
    MyMerkleCompress::new(get_poseidon16().clone())
}

pub fn build_prover_state<EF: ExtensionField<KoalaBear>>()
-> ProverState<KoalaBear, EF, MyChallenger> {
    ProverState::new(build_challenger())
}

pub fn build_verifier_state<EF: ExtensionField<KoalaBear>>(
    prover_state: &ProverState<KoalaBear, EF, MyChallenger>,
) -> VerifierState<KoalaBear, EF, MyChallenger> {
    VerifierState::new(prover_state.proof_data().to_vec(), build_challenger())
}

pub trait ToUsize {
    fn to_usize(self) -> usize;
}

impl<F: PrimeField64> ToUsize for F {
    fn to_usize(self) -> usize {
        self.as_canonical_u64() as usize
    }
}
