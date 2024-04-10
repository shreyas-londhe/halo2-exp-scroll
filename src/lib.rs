use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
    plonk::{Circuit, Column, ConstraintSystem, Error, Instance},
};

#[derive(Clone)]
pub struct ExpConfig {
    instance: Column<Instance>,
}

impl ExpConfig {
    pub fn configure<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            instance: meta.instance_column(),
        }
    }

    pub fn assign<F: FieldExt>(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(|| "halo2-exp-region", |mut region| Err(Error::Synthesis))
    }

    pub fn expose_public<F: FieldExt>(
        &self,
        layouter: &mut impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        offset: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.instance, offset)
    }
}

#[derive(Default)]
struct ExpCircuit<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for ExpCircuit<F> {
    type Config = ExpConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        ExpConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let offset = 0; // offset of result (TBD)
        let result = config.assign(&mut layouter)?;
        config.expose_public(&mut layouter, &result, offset)
    }
}

#[cfg(test)]
mod tests {
    use crate::ExpCircuit;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pasta::Fp;

    #[test]
    fn test_exp_circuit_pass() {
        let k = 3;
        let public_inputs = vec![
            Fp::from(2), // base
            Fp::from(3), // exponent
            Fp::from(8), // exponentiation
        ];
        let circuit = ExpCircuit::<Fp>::default();
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    #[should_panic]
    fn test_exp_circuit_fail() {
        let k = 3;
        let public_inputs = vec![
            Fp::from(2), // base
            Fp::from(3), // exponent
            Fp::from(7), // exponentiation
        ];
        let circuit = ExpCircuit::<Fp>::default();
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied()
    }
}
