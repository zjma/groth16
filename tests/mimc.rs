#![warn(unused)]
#![deny(
    trivial_casts,
    trivial_numeric_casts,
    variant_size_differences,
    stable_features,
    non_shorthand_field_patterns,
    renamed_and_removed_lints,
    private_in_public,
    unsafe_code
)]

use std::ops::{AddAssign, SubAssign};
// For randomness (during paramgen and proof generation)
use ark_std::rand::Rng;

// For benchmarking
use std::time::{Duration, Instant};

// Bring in some tools for using pairing-friendly curves
// We're going to use the BLS12-377 pairing-friendly elliptic curve.
use ark_bls12_381::{Bls12_381, Fq12, Fr};
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ec::AffineCurve;
use ark_ec::group::Group;
use ark_ff::{Field, Fp12, Zero};
use ark_std::test_rng;

// We'll use these interfaces to construct our circuit.
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};
use ark_serialize::CanonicalSerialize;

const MIMC_ROUNDS: usize = 322;

/// This is an implementation of MiMC, specifically a
/// variant named `LongsightF322p3` for BLS12-377.
/// See http://eprint.iacr.org/2016/492 for more
/// information about this construction.
///
/// ```
/// function LongsightF322p3(xL ⦂ Fp, xR ⦂ Fp) {
///     for i from 0 up to 321 {
///         xL, xR := xR + (xL + Ci)^3, xL
///     }
///     return xL
/// }
/// ```
fn mimc<F: Field>(mut xl: F, mut xr: F, constants: &[F]) -> F {
    assert_eq!(constants.len(), MIMC_ROUNDS);

    for i in 0..MIMC_ROUNDS {
        let mut tmp1 = xl;
        tmp1.add_assign(&constants[i]);
        let mut tmp2 = tmp1;
        tmp2.square_in_place();
        tmp2.mul_assign(&tmp1);
        tmp2.add_assign(&xr);
        xr = xl;
        xl = tmp2;
    }

    xl
}

/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
struct MiMCDemo<'a, F: Field> {
    xl: Option<F>,
    xr: Option<F>,
    constants: &'a [F],
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, F: Field> ConstraintSynthesizer<F> for MiMCDemo<'a, F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        assert_eq!(self.constants.len(), MIMC_ROUNDS);

        // Allocate the first component of the preimage.
        let mut xl_value = self.xl;
        let mut xl =
            cs.new_witness_variable(|| xl_value.ok_or(SynthesisError::AssignmentMissing))?;

        // Allocate the second component of the preimage.
        let mut xr_value = self.xr;
        let mut xr =
            cs.new_witness_variable(|| xr_value.ok_or(SynthesisError::AssignmentMissing))?;

        for i in 0..MIMC_ROUNDS {
            // xL, xR := xR + (xL + Ci)^3, xL
            let ns = ns!(cs, "round");
            let cs = ns.cs();

            // tmp = (xL + Ci)^2
            let tmp_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.square_in_place();
                e
            });
            let tmp =
                cs.new_witness_variable(|| tmp_value.ok_or(SynthesisError::AssignmentMissing))?;

            cs.enforce_constraint(
                lc!() + xl + (self.constants[i], Variable::One),
                lc!() + xl + (self.constants[i], Variable::One),
                lc!() + tmp,
            )?;

            // new_xL = xR + (xL + Ci)^3
            // new_xL = xR + tmp * (xL + Ci)
            // new_xL - xR = tmp * (xL + Ci)
            let new_xl_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.mul_assign(&tmp_value.unwrap());
                e.add_assign(&xr_value.unwrap());
                e
            });

            let new_xl = if i == (MIMC_ROUNDS - 1) {
                // This is the last round, xL is our image and so
                // we allocate a public input.
                cs.new_input_variable(|| new_xl_value.ok_or(SynthesisError::AssignmentMissing))?
            } else {
                cs.new_witness_variable(|| new_xl_value.ok_or(SynthesisError::AssignmentMissing))?
            };

            cs.enforce_constraint(
                lc!() + tmp,
                lc!() + xl + (self.constants[i], Variable::One),
                lc!() + new_xl - xr,
            )?;

            // xR = xL
            xr = xl;
            xr_value = xl_value;

            // xL = new_xL
            xl = new_xl;
            xl_value = new_xl_value;
        }

        Ok(())
    }
}

#[test]
fn test_mimc_gm_17() {
    // We're going to use the Groth-Maller17 proving system.
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };

    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let rng = &mut test_rng();

    // Generate the MiMC round constants
    let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();

    println!("Creating parameters...");

    // Create parameters for our circuit
    let params = {
        let c = MiMCDemo::<Fr> {
            xl: None,
            xr: None,
            constants: &constants,
        };

        generate_random_parameters::<Bls12_381, _, _>(c, rng).unwrap()
    };

    for x in params.vk.gamma_abc_g1.iter() {
        let mut buf = vec![];
        x.serialize_uncompressed(&mut buf);
        println!("gamma_abc_g1={}", hex::encode(buf));
    }

    let mut buf = vec![];
    params.vk.alpha_g1.serialize_uncompressed(&mut buf);
    println!("alpha_g1={}", hex::encode(buf));

    let mut buf = vec![];
    params.vk.beta_g2.serialize_uncompressed(&mut buf);
    println!("beta_g2={}", hex::encode(buf));

    let mut buf = vec![];
    params.vk.gamma_g2.serialize_uncompressed(&mut buf);
    println!("gamma_g2={}", hex::encode(buf));

    let mut buf = vec![];
    params.vk.delta_g2.serialize_uncompressed(&mut buf);
    println!("delta_g2={}", hex::encode(buf));



    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    // Let's benchmark stuff!
    const SAMPLES: u32 = 1;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    // let mut proof_vec = vec![];

    for _ in 0..SAMPLES {
        // Generate a random preimage and compute the image
        let xl = rng.gen();
        let xr = rng.gen();
        let image: Fr = mimc(xl, xr, &constants);
        let mut buf = vec![];
        image.serialize_uncompressed(&mut buf);
        println!("image={}", hex::encode(buf));
        // proof_vec.truncate(0);

        let start = Instant::now();
        {
            // Create an instance of our circuit (with the
            // witness)
            let c = MiMCDemo {
                xl: Some(xl),
                xr: Some(xr),
                constants: &constants,
            };

            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, &params, rng).unwrap();
            let mut buf = vec![];
            proof.a.serialize_uncompressed(&mut buf);
            println!("proof.a={}", hex::encode(buf));
            let mut buf = vec![];
            proof.b.serialize_uncompressed(&mut buf);
            println!("proof.b={}", hex::encode(buf));
            let mut buf = vec![];
            proof.c.serialize_uncompressed(&mut buf);
            println!("proof.c={}", hex::encode(buf));

            assert!(verify_proof(&pvk, &proof, &[image.clone()]).unwrap());

            // Verifying manually using the original equation in groth16 paper.
            let left = Bls12_381::pairing(proof.a.clone(), proof.b.clone());
            let mut buf = vec![];
            left.serialize(&mut buf);
            println!("left={}", hex::encode(buf));

            let right_1 = Bls12_381::pairing(params.vk.alpha_g1.clone(), params.vk.beta_g2.clone());
            let mut buf = vec![];
            right_1.serialize(&mut buf);
            println!("right_1={}", hex::encode(buf));

            let right_3 = Bls12_381::pairing(proof.c, params.vk.delta_g2.clone());
            let mut buf = vec![];
            right_3.serialize(&mut buf);
            println!("right_3={}", hex::encode(buf));

            let shit = (params.vk.gamma_abc_g1.get(0).unwrap().clone().into_projective() + params.vk.gamma_abc_g1.get(1).unwrap().clone().mul(image.clone())).into_affine();
            let mut buf = vec![];
            shit.serialize(&mut buf);
            println!("shit={}", hex::encode(buf));

            let right_2 = Bls12_381::pairing(shit, params.vk.gamma_g2.clone());
            let mut buf = vec![];
            right_2.serialize(&mut buf);
            println!("right_2={}", hex::encode(buf));

            let mut right = (right_1 * right_2 * right_3);
            assert_eq!(left, right);
        }

        total_proving += start.elapsed();

        let start = Instant::now();
        // let proof = Proof::read(&proof_vec[..]).unwrap();
        // Check the proof

        total_verifying += start.elapsed();
    }
    let proving_avg = total_proving / SAMPLES;
    let proving_avg =
        proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg =
        verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

    println!("Average proving time: {:?} seconds", proving_avg);
    println!("Average verifying time: {:?} seconds", verifying_avg);
}
