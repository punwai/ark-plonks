use ark_ec::{scalar_mul::variable_base::{VariableBaseMSM}, bls12::G1Prepared, Group};
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain, EvaluationDomain, DenseUVPolynomial, domain};
use ark_bls12_381::{G1Projective as G, Fr as F, G1Affine};
use ark_std::rand::distributions::Distribution;
use ark_relations::r1cs::Field;
use ark_std::{Zero, One};

struct TrustedSetupParameters {
    t: Vec<G>
}

struct ProvingStatement {
    pub n: u64,
    pub qm: DensePolynomial<F>,
    pub ql: DensePolynomial<F>,
    pub qr: DensePolynomial<F>,
    pub qo: DensePolynomial<F>,
    pub qc: DensePolynomial<F>,
    pub s_sig1: DensePolynomial<F>,
    pub s_sig2: DensePolynomial<F>,
    pub s_sig3: DensePolynomial<F>,
    pub srs: TrustedSetupParameters
}

struct Round1Message {
    a_commit: G,
    b_commit: G,
    c_commit: G,
}

struct Round2Message {
    z_commit: G
}

struct Round3Message {
    t_lo_commit: G,
    t_mid_commit: G,
    t_hi_commit: G,
}

struct Prover {
}

fn setup(
    n: u64,
    qm: Vec<F>,
    ql: Vec<F>,
    qr: Vec<F>,
    qo: Vec<F>,
    qc: Vec<F>
) -> ProvingStatement {
    let eval = GeneralEvaluationDomain::<F>::new(n as usize).unwrap();
    let qm_poly = DensePolynomial::from_coefficients_vec(eval.ifft(&qm));
    let ql_poly = DensePolynomial::from_coefficients_vec(eval.ifft(&ql));
    let qr_poly = DensePolynomial::from_coefficients_vec(eval.ifft(&qr));
    let qo_poly = DensePolynomial::from_coefficients_vec(eval.ifft(&qo));
    let qc_poly = DensePolynomial::from_coefficients_vec(eval.ifft(&qc));
    let s_sig1 = DensePolynomial::from_coefficients_vec(
        eval.ifft(&(0..n).map(|x| F::from(x)).collect::<Vec<_>>())
    );
    let s_sig2 = DensePolynomial::from_coefficients_vec(
        eval.ifft(&(n..(2 * n)).map(|x| F::from(x)).collect::<Vec<_>>())
    );
    let s_sig3 = DensePolynomial::from_coefficients_vec(
        eval.ifft(&((2 * n)..(3 * n)).map(|x| F::from(x)).collect::<Vec<_>>())
    );

    // TOXIC WASTE
    // PLEASE FIX
    let x = F::from(1234567u64);
    
    let mut x_pow = F::from(1);
    let mut trusted_setup_params = vec![];
    for i in 0..(n + 5) {
        trusted_setup_params.push(
            G::default() * x_pow
        );
        x_pow *= x;
    }
    let tst = TrustedSetupParameters {
        t: trusted_setup_params
    };
    ProvingStatement {
        n: n,
        qm: qm_poly,
        ql: ql_poly,
        qr: qr_poly,
        qo: qo_poly,
        qc: qc_poly,
        s_sig1,
        s_sig2,
        s_sig3,
        srs: tst,
    }
}

fn eval_trusted(coeffs: &Vec<F>, statement: &ProvingStatement) -> G {
    G::msm(
        &statement.srs.t[..coeffs.len()].iter().map(|x| G1Affine::from(*x)).collect::<Vec<_>>(),
        &coeffs
    ).unwrap()
}

// Roots of unity
fn round_1(witness: &Vec<F>, statement: &ProvingStatement) -> Round1Message {
    let n = statement.n as usize;
    let eval = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let a = eval.ifft(&witness[..n]);
    let b = eval.ifft(&witness[n..(2 * n)]);
    let c = eval.ifft(&witness[(2 * n)..(3 * n)]);
    let a_eval = eval_trusted(&a, &statement);
    let b_eval = eval_trusted(&b, &statement);
    let c_eval = eval_trusted(&c, &statement);
    Round1Message { 
        a_commit: a_eval,
        b_commit: b_eval,
        c_commit: c_eval,
    }
}

// Takes a bunch of coefficients and extends the basis by 4x
fn extend_lagrange_basis(evals: &[F], cofactor: &F) -> Vec<F> {
    // Check that 
    let n = evals.len();
    let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let group_order = domain.size();
    let mut coeffs = (domain.ifft(evals)).into_iter().map(|x| x * cofactor).collect::<Vec<_>>();
    coeffs.extend(vec![F::zero(); group_order * 3]);
    let domain = GeneralEvaluationDomain::<F>::new(group_order * 4).unwrap();
    domain.fft(&coeffs)
}

fn round_2(witness: &Vec<F>, statement: &ProvingStatement, beta: &F, lambda: &F) -> Round2Message {
    let n = statement.n as usize;
    let mut z_evals = vec![];
    z_evals.push(F::one());

    let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let mut w = domain.group_gen();
    for i in 0..(n - 1) {
        // Root of unity +
        let coeff = (witness[i] + lambda) * (witness[n + i] + lambda) * (witness[n + i] + lambda);
        z_evals.push(coeff);
        w *= domain.group_gen();
    }
    let z = domain.ifft(&z_evals);
    return Round2Message { 
        z_commit: eval_trusted(&z, &statement)
    }
}

fn round_3(
    witness: &Vec<F>,
    statement: &ProvingStatement,
    public_inputs: &Vec<F>,
    z_evals: &Vec<F>,
    alpha: &F,
    beta: &F,
    gamma: &F,
    fft_cofactor: &F,
) -> Round3Message {
    let n = statement.n as usize;
    let a = &witness[..n];
    let b = &witness[n..(2 * n)];
    let c = &witness[(2 * n)..(3 * n)];

    let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let group_order = domain.size();

    let mut quotient = vec![];
    // This is incorrect, you cannot compute the multiplication like this?
    // A way that you can do this is to 

    let a_big = extend_lagrange_basis(a, fft_cofactor);
    let b_big = extend_lagrange_basis(b, fft_cofactor);
    let c_big = extend_lagrange_basis(c, fft_cofactor);
    let ql_big = extend_lagrange_basis(&statement.ql, fft_cofactor);
    let qr_big = extend_lagrange_basis(&statement.qr, fft_cofactor);
    let qo_big = extend_lagrange_basis(&statement.qo, fft_cofactor);
    let qc_big = extend_lagrange_basis(&statement.qc, fft_cofactor);
    let pi_big = extend_lagrange_basis(public_inputs, fft_cofactor);
    let z_big = extend_lagrange_basis(z_evals, fft_cofactor);
    let s1_big = extend_lagrange_basis(&statement.s_sig1, fft_cofactor);
    let s2_big = extend_lagrange_basis(&statement.s_sig2, fft_cofactor);
    let s3_big = extend_lagrange_basis(&statement.s_sig3, fft_cofactor);

    for i in 0..(group_order * 4) {
        let eval = a_big[i] * b_big[i] * statement.qm[i]
            + a_big[i] * ql_big[i]
            + b_big[i] * qr_big[i]
            + c_big[i] * qo_big[i]
            + pi_big[i]
            + qc_big[i];
        quotient.push(eval);
    }

    let mut left_check = vec![];
    let mut right_check = vec![];

    let quarter_domain = GeneralEvaluationDomain::<F>::new(group_order * 4).unwrap();
    let quarter_root = quarter_domain.group_gen();

    let schwazip = |a, b| a + b * beta + gamma;

    for i in 0..(group_order * 4) {
        let eval = schwazip(a_big[i], quarter_root * fft_cofactor)
                   * schwazip(b_big[i], quarter_root * F::from(2) * fft_cofactor)
                   * schwazip(c_big[i], quarter_root * F::from(3) * fft_cofactor) * z_big[i];
        left_check.push(eval);
        let eval = schwazip(a_big[i], s1_big[i])
                   * schwazip(b_big[i], s2_big[i])
                   * schwazip(c_big[i], s3_big[i]) * z_big[(i + 4) % (group_order * 4)];
        right_check.push(eval);
    }
    let mut t_eval = vec![];

    // Compute ZH_big
    let mut ZH_big = vec![];
    let mut root = quarter_root;
    for _ in 0..(group_order * 4) {
        ZH_big.push(
            (quarter_root * fft_cofactor).pow(vec![(group_order - 1) as u64])
        );
        root *= quarter_root;
    }

    let mut L0 = vec![F::one()];
    L0.extend(&vec![F::zero(); group_order - 1]);
    let L0_big = extend_lagrange_basis(&L0, fft_cofactor);

    let mut permutation_first_row = vec![];
    for i in 0..(group_order * 4) {
        permutation_first_row.push(
            (z_big[i] - F::one()) * L0_big[i]
        )
    }

    for i in 0..(group_order * 4) {
        t_eval.push(
            (quotient[i] + alpha * &(left_check[i] - &right_check[i]) + alpha * alpha * permutation_first_row[i]) / ZH_big[i]
        );
    }

    let go = group_order as usize;
    let t_coeffs = quarter_domain.ifft(&t_eval);
    let t1 = domain.fft(&t_coeffs[..go]);
    let t2 = domain.fft(&t_coeffs[go..(go* 2)]);
    let t3 = domain.fft(&t_coeffs[(group_order * 2)..(group_order * 3)]);
    
    Round3Message {
        t_lo_commit: G::generator(),
        t_mid_commit: G::generator(),
        t_hi_commit: G::generator(),
    }
}

fn main() {
    // a
    let domain = GeneralEvaluationDomain::<F>::new(1000).unwrap();
    let z = domain.vanishing_polynomial();

    let n = 2;
    let qm = vec![1, 0];
    let ql = vec![0, 1];
    let qr = vec![0, -1];
    let qo = vec![1, 0];
    let qc = vec![0, 0];

    // let setup_params = setup();
    println!("z = {:?}", z);
    // Perform FFT over a to get a_poly
}
