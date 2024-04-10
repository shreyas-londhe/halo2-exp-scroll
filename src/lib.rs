use halo2_proofs::{
    circuit::{ AssignedCell, Layouter, SimpleFloorPlanner, Value },
    pasta::group::ff::PrimeField,
    plonk::{ Advice, Circuit, Column, ConstraintSystem, Error, Expression, Instance, Selector },
    poly::Rotation,
};

// Step:
// 1. Assign exp_bits (BE) to cells, as well as the base and result values.
// 2. Prove the correctness of the exponentiation:
//    - Initialize the result (res) to 1
//    - For each bit in the exponent:
//       - If the bit is 0, square the current result (res = res * res)
//       - If the bit is 1, square and multiply the current result by base (res = res * res * base)
//    - Constrain the final result to match the provided result value

// Initial state:
// exp | base | start | end
// 0   | b    | 1     | 1
// 1   | b    | 1     | b
// 0   | b    | b     | b^2
// 1   | b    | b^2   | b^3

#[derive(Clone)]
pub struct ExpConfig {
    bit_selector: Selector,
    exp_selector: Selector,
    advice: [Column<Advice>; 4],
    instance: Column<Instance>,
}

impl ExpConfig {
    pub fn configure<F: PrimeField>(meta: &mut ConstraintSystem<F>) -> Self {
        let bit_selector = meta.selector();
        let exp_selector = meta.selector();

        let col_bit = meta.advice_column();
        let col_base = meta.advice_column();
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let instance = meta.instance_column();

        meta.enable_equality(col_bit);
        meta.enable_equality(col_base);
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(instance);

        meta.create_gate("bit constraint", |meta| {
            let s = meta.query_selector(bit_selector);
            let bit = meta.query_advice(col_bit, Rotation::cur());

            vec![s * (bit.clone() * (Expression::Constant(F::from(1)) - bit))]
        });

        meta.create_gate("square multiply constraint", |meta| {
            let s = meta.query_selector(exp_selector);
            let base = meta.query_advice(col_base, Rotation::cur());
            let bit = meta.query_advice(col_bit, Rotation::cur());
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());

            vec![
                s *
                    (a.clone() * a.clone() * (Expression::Constant(F::from(1u64)) - bit.clone()) +
                        a.clone() * a * base * bit -
                        b)
            ]
        });

        Self {
            bit_selector,
            exp_selector,
            advice: [col_bit, col_base, col_a, col_b],
            instance,
        }
    }

    pub fn assign_first_row<F: PrimeField>(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: Value<F>,
        base: Value<F>
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "assign first row",
            |mut region| {
                self.bit_selector.enable(&mut region, 0)?;
                self.exp_selector.enable(&mut region, 0)?;

                region.assign_advice(
                    || "assign bit",
                    self.advice[0],
                    0,
                    || bit
                )?;

                let base_cell = region.assign_advice(
                    || "assign base",
                    self.advice[1],
                    0,
                    || base
                )?;

                region.assign_advice(
                    || "assign one",
                    self.advice[2],
                    0,
                    || Value::known(F::ONE)
                )?;

                let res_cell = region.assign_advice(
                    || "assign res",
                    self.advice[3],
                    0,
                    || Value::known(F::ONE) - bit + base * bit
                )?;

                Ok((base_cell, res_cell))
            }
        )
    }

    pub fn exp_prove_layer<F: PrimeField>(
        &self,
        layouter: &mut impl Layouter<F>,
        bit: Value<F>,
        base_cell: AssignedCell<F, F>,
        res_cell: AssignedCell<F, F>
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "exp prove layer",
            |mut region| {
                self.bit_selector.enable(&mut region, 0)?;
                self.exp_selector.enable(&mut region, 0)?;

                region.assign_advice(
                    || "assign bit",
                    self.advice[0],
                    0,
                    || bit
                )?;

                base_cell.copy_advice(|| "copy base", &mut region, self.advice[1], 0)?;

                let start_cell = res_cell.copy_advice(
                    || "copy start",
                    &mut region,
                    self.advice[2],
                    0
                )?;

                let base = base_cell.value().map(|x| x.to_owned());
                let start = start_cell.value().map(|x| x.to_owned());

                let end_cell = region.assign_advice(
                    || "assign end",
                    self.advice[3],
                    0,
                    || start * start * (Value::known(F::ONE) - bit) + start * start * base * bit
                )?;

                Ok(end_cell)
            }
        )
    }

    pub fn expose_public<F: PrimeField>(
        &self,
        layouter: &mut impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        offset: usize
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.instance, offset)?;

        Ok(())
    }
}

#[derive(Default)]
struct ExpCircuit<F> {
    base: Value<F>,
    exp_bits: Vec<Value<F>>, // big-endian
}

impl<F: PrimeField> Circuit<F> for ExpCircuit<F> {
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
        mut layouter: impl Layouter<F>
    ) -> Result<(), Error> {
        let (base_cell, mut res_cell) = config.assign_first_row(
            &mut layouter,
            self.exp_bits[0],
            self.base
        )?;

        for bit in self.exp_bits.iter().skip(1) {
            res_cell = config.exp_prove_layer(&mut layouter, *bit, base_cell.clone(), res_cell)?;
        }

        config.expose_public(&mut layouter, &res_cell, 0)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::ExpCircuit;
    use halo2_proofs::circuit::Value;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pasta::Fp;

    #[test]
    fn test_exp_circuit_pass() {
        // 2^3 = 8

        let k = 4;
        let public_inputs = vec![Fp::from(8)];
        let circuit = ExpCircuit::<Fp> {
            base: Value::known(Fp::from(2)),
            exp_bits: vec![
                Value::known(Fp::from(0)),
                Value::known(Fp::from(1)),
                Value::known(Fp::from(1))
            ],
        };
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    #[should_panic]
    fn test_exp_circuit_fail() {
        // 2^3 = 8

        let k = 4;
        let public_inputs = vec![Fp::from(8)];
        let circuit = ExpCircuit::<Fp> {
            base: Value::known(Fp::from(2)),
            exp_bits: vec![
                Value::known(Fp::from(0)),
                Value::known(Fp::from(1)),
                Value::known(Fp::from(0))
            ],
        };
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }
}
