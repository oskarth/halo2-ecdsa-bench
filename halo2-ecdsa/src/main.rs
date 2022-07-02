// Based on https://github.com/privacy-scaling-explorations/halo2wrong/blob/master/ecdsa/src/ecdsa.rs
//
use halo2_proofs;
use integer;
use maingate;
use halo2_proofs::arithmetic::{CurveAffine, FieldExt};
use halo2_proofs::halo2curves::bn256::Fr as BnScalar;
use halo2_proofs::halo2curves::secp256k1::Secp256k1Affine as Secp256k1;
use halo2_proofs::plonk::{Circuit, ConstraintSystem, Error};
use halo2_proofs::dev::MockProver;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use group::ff::Field;
use group::{Curve, Group};
use rand_core::OsRng;
use std::marker::PhantomData;
use ecc::maingate::{big_to_fe, fe_to_big};
use ecc::{EccConfig, GeneralEccChip};
use ecc::maingate::RegionCtx;
use ecc::integer::Range;
use ecdsa::ecdsa::{AssignedEcdsaSig, AssignedPublicKey, EcdsaChip};
use integer::{IntegerInstructions, NUMBER_OF_LOOKUP_LIMBS};
use maingate::{MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions};

const BIT_LEN_LIMB: usize = 68;
const NUMBER_OF_LIMBS: usize = 4;

#[derive(Clone, Debug)]
struct TestCircuitEcdsaVerifyConfig {
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
}

impl TestCircuitEcdsaVerifyConfig {
    pub fn new<C: CurveAffine, N: FieldExt>(meta: &mut ConstraintSystem<N>) -> Self {
        let (rns_base, rns_scalar) =
            GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();
        let main_gate_config = MainGate::<N>::configure(meta);
        let mut overflow_bit_lengths: Vec<usize> = vec![];
        overflow_bit_lengths.extend(rns_base.overflow_lengths());
        overflow_bit_lengths.extend(rns_scalar.overflow_lengths());
        let range_config =
            RangeChip::<N>::configure(meta, &main_gate_config, overflow_bit_lengths);
        TestCircuitEcdsaVerifyConfig {
            main_gate_config,
            range_config,
        }
    }

    pub fn ecc_chip_config(&self) -> EccConfig {
        EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }

    pub fn config_range<N: FieldExt>(
        &self,
        layouter: &mut impl Layouter<N>,
    ) -> Result<(), Error> {
        let bit_len_lookup = BIT_LEN_LIMB / NUMBER_OF_LOOKUP_LIMBS;
        let range_chip = RangeChip::<N>::new(self.range_config.clone(), bit_len_lookup);
        range_chip.load_limb_range_table(layouter)?;
        range_chip.load_overflow_range_tables(layouter)?;

        Ok(())
    }
}

#[derive(Default, Clone)]
struct TestCircuitEcdsaVerify<E: CurveAffine, N: FieldExt> {
    public_key: Value<E>,
    signature: Value<(E::Scalar, E::Scalar)>,
    msg_hash: Value<E::Scalar>,

    aux_generator: E,
    window_size: usize,
    _marker: PhantomData<N>,
}

impl<E: CurveAffine, N: FieldExt> Circuit<N> for TestCircuitEcdsaVerify<E, N> {
    type Config = TestCircuitEcdsaVerifyConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
        TestCircuitEcdsaVerifyConfig::new::<E, N>(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<N>,
    ) -> Result<(), Error> {
        let mut ecc_chip = GeneralEccChip::<E, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(
            config.ecc_chip_config(),
        );
        let scalar_chip = ecc_chip.scalar_field_chip();

        layouter.assign_region(
            || "assign aux values",
            |mut region| {
                let offset = &mut 0;
                let ctx = &mut RegionCtx::new(&mut region, offset);

                ecc_chip.assign_aux_generator(ctx, Value::known(self.aux_generator))?;
                ecc_chip.assign_aux(ctx, self.window_size, 1)?;
                Ok(())
            },
        )?;

        let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());

        layouter.assign_region(
            || "region 0",
            |mut region| {
                let offset = &mut 0;
                let ctx = &mut RegionCtx::new(&mut region, offset);

                let r = self.signature.map(|signature| signature.0);
                let s = self.signature.map(|signature| signature.1);
                let integer_r = ecc_chip.new_unassigned_scalar(r);
                let integer_s = ecc_chip.new_unassigned_scalar(s);
                let msg_hash = ecc_chip.new_unassigned_scalar(self.msg_hash);

                let r_assigned =
                    scalar_chip.assign_integer(ctx, integer_r, Range::Remainder)?;
                let s_assigned =
                    scalar_chip.assign_integer(ctx, integer_s, Range::Remainder)?;
                let sig = AssignedEcdsaSig {
                    r: r_assigned,
                    s: s_assigned,
                };

                let pk_in_circuit = ecc_chip.assign_point(ctx, self.public_key)?;
                let pk_assigned = AssignedPublicKey {
                    point: pk_in_circuit,
                };
                let msg_hash = scalar_chip.assign_integer(ctx, msg_hash, Range::Remainder)?;
                ecdsa_chip.verify(ctx, &sig, &pk_assigned, &msg_hash)
            },
        )?;

        config.config_range(&mut layouter)?;

        Ok(())
    }
}

fn mod_n<C: CurveAffine>(x: C::Base) -> C::Scalar {
    let x_big = fe_to_big(x);
    big_to_fe(x_big)
}

fn run<C: CurveAffine, N: FieldExt>() {
    let g = C::generator();

    // Generate a key pair
    let sk = <C as CurveAffine>::ScalarExt::random(OsRng);
    let public_key = (g * sk).to_affine();

    // Generate a valid signature
    // Suppose `m_hash` is the message hash
    let msg_hash = <C as CurveAffine>::ScalarExt::random(OsRng);

    // Draw arandomness
    let k = <C as CurveAffine>::ScalarExt::random(OsRng);
    let k_inv = k.invert().unwrap();

    // Calculate `r`
    let r_point = (g * k).to_affine().coordinates().unwrap();
    let x = r_point.x();
    let r = mod_n::<C>(*x);

    // Calculate `s`
    let s = k_inv * (msg_hash + (r * sk));

    // Sanity check. Ensure we construct a valid signature. So lets verify it
    {
        let s_inv = s.invert().unwrap();
        let u_1 = msg_hash * s_inv;
        let u_2 = r * s_inv;
        let r_point = ((g * u_1) + (public_key * u_2))
            .to_affine()
            .coordinates()
            .unwrap();
        let x_candidate = r_point.x();
        let r_candidate = mod_n::<C>(*x_candidate);
        assert_eq!(r, r_candidate);
    }

    let k = 20;
    let aux_generator = C::CurveExt::random(OsRng).to_affine();
    let circuit = TestCircuitEcdsaVerify::<C, N> {
        public_key: Value::known(public_key),
        signature: Value::known((r, s)),
        msg_hash: Value::known(msg_hash),
        aux_generator,
        window_size: 2,
        _marker: PhantomData,
    };

    let public_inputs = vec![vec![]];
    let prover = match MockProver::run(k, &circuit, public_inputs) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    assert_eq!(prover.verify(), Ok(()));
}

#[cfg(feature = "dev-graph")]
fn plot<C: CurveAffine, N: FieldExt>() {
    println!("Run plot");
    let g = C::generator();

    // Generate a key pair
    let sk = <C as CurveAffine>::ScalarExt::random(OsRng);
    let public_key = (g * sk).to_affine();

    println!("Public key {:?}", public_key);

    // Generate a valid signature
    // Suppose `m_hash` is the message hash
    let msg_hash = <C as CurveAffine>::ScalarExt::random(OsRng);

    println!("Msg hash{:?}", msg_hash);

    // Draw arandomness
    let k = <C as CurveAffine>::ScalarExt::random(OsRng);
    let k_inv = k.invert().unwrap();

    // Calculate `r`
    let r_point = (g * k).to_affine().coordinates().unwrap();
    let x = r_point.x();
    let r = mod_n::<C>(*x);

    // Calculate `s`
    let s = k_inv * (msg_hash + (r * sk));

    println!("r {:?}, s {:?}", r, s);

    // Sanity check. Ensure we construct a valid signature. So lets verify it
    {
        let s_inv = s.invert().unwrap();
        let u_1 = msg_hash * s_inv;
        let u_2 = r * s_inv;
        let r_point = ((g * u_1) + (public_key * u_2))
            .to_affine()
            .coordinates()
            .unwrap();
        let x_candidate = r_point.x();
        let r_candidate = mod_n::<C>(*x_candidate);
        assert_eq!(r, r_candidate);
    }

    // What is k?
    let k = 20;
    let aux_generator = C::CurveExt::random(OsRng).to_affine();
    let circuit = TestCircuitEcdsaVerify::<C, N> {
        public_key: Value::known(public_key),
        signature: Value::known((r, s)),
        msg_hash: Value::known(msg_hash),
        aux_generator,
        window_size: 2,
        _marker: PhantomData,
    };

    use plotters::prelude::*;

    let root = BitMapBackend::new("ecdsa-layout.png", (1024, 3096)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("ECDSA Layout", ("sans-serif", 60)).unwrap();

    halo2_proofs::dev::CircuitLayout::default()
        .render(20, &circuit, &root)
        .unwrap();
}

fn main() {
    #[cfg(feature = "dev-graph")]
    plot::<Secp256k1, BnScalar>();

    println!("Run ECDSA verify");
    run::<Secp256k1, BnScalar>();

}
