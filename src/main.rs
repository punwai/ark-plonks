use ark_ec::{scalar_mul::variable_base::{VariableBaseMSM}, bls12::G1Prepared, Group};
use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain, EvaluationDomain, DenseUVPolynomial, domain, Polynomial};
use ark_bls12_381::{G1Projective as G, Fr as F, G1Affine};
use ark_std::rand::distributions::Distribution;
use ark_relations::r1cs::Field;
use ark_std::{Zero, One};
use std::{ops::{Mul, Sub, Neg}, time::Instant};


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
    pub permutation: Vec<F>,
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

struct Round4Message {
    a_hat: F,
    b_hat: F,
    c_hat: F,
    s_sig1_hat: F,
    s_sig2_hat: F,
    s_sig3_hat: F,
    zw_hat: F
}

struct Round5Message {
    W_commit: G,
    W_zw_commit: G,
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
    let n = n as usize;
    let eval = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let qm_poly = DensePolynomial::from_coefficients_vec(eval.ifft(&qm));
    let ql_poly = DensePolynomial::from_coefficients_vec(eval.ifft(&ql));
    let qr_poly = DensePolynomial::from_coefficients_vec(eval.ifft(&qr));
    let qo_poly = DensePolynomial::from_coefficients_vec(eval.ifft(&qo));
    let qc_poly = DensePolynomial::from_coefficients_vec(eval.ifft(&qc));
    let permutation = (0..(3 * n)).map(|x| F::from(x as u64)).collect::<Vec<_>>();
    let s_sig1 = DensePolynomial { coeffs: eval.ifft(&permutation[0..n]) };
    let s_sig2 = DensePolynomial { coeffs: eval.ifft(&permutation[n..(2 * n)]) };
    let s_sig3 = DensePolynomial { coeffs: eval.ifft(&permutation[(2 * n)..(3 * n)]) };

    // TOXIC WASTE
    // PLEASE FIX
    let x = F::from(1234567u64);
    
    let mut x_pow = F::from(1);
    let mut trusted_setup_params = vec![];

    let domain_size = eval.size();
    for i in 0..(domain_size + 5) {
        trusted_setup_params.push(
            G::default() * x_pow
        );
        x_pow *= x;
    }
    let tst = TrustedSetupParameters {
        t: trusted_setup_params
    };
    ProvingStatement {
        n: n as u64,
        qm: qm_poly,
        ql: ql_poly,
        qr: qr_poly,
        qo: qo_poly,
        qc: qc_poly,
        permutation,
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

struct Transcript {
    a: DensePolynomial<F>,
    b: DensePolynomial<F>,
    c: DensePolynomial<F>,
    z: DensePolynomial<F>,
    z_evals: Vec<F>,
    t1: DensePolynomial<F>,
    t2: DensePolynomial<F>,
    t3: DensePolynomial<F>,
    alpha: F,
    beta: F,
    gamma: F,
    mu: F,
    zeta: F,
    fft_cofactor: F,
}

impl Transcript {
    fn new() -> Self {
        Self {
            a: DensePolynomial::<F>::zero(),
            b: DensePolynomial::<F>::zero(),
            c: DensePolynomial::<F>::zero(),
            z: DensePolynomial::<F>::zero(),
            t1: DensePolynomial::<F>::zero(),
            t2: DensePolynomial::<F>::zero(),
            t3: DensePolynomial::<F>::zero(),
            alpha: F::zero(),
            beta: F::zero(),
            gamma: F::zero(),
            mu: F::zero(),
            zeta: F::zero(),
            fft_cofactor: F::zero(),
            z_evals: vec![]
        }
    }
}

// Roots of unity
fn round_1(witness: &Vec<F>, statement: &ProvingStatement, transcript: &mut Transcript) -> Round1Message {
    let n = statement.n as usize;
    let eval = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let a = eval.ifft(&witness[..n]);
    let b = eval.ifft(&witness[n..(2 * n)]);
    let c = eval.ifft(&witness[(2 * n)..(3 * n)]);
    let a_eval = eval_trusted(&a, &statement);
    let b_eval = eval_trusted(&b, &statement);
    let c_eval = eval_trusted(&c, &statement);
    transcript.a = DensePolynomial { coeffs: a };
    transcript.b = DensePolynomial { coeffs: b };
    transcript.c = DensePolynomial { coeffs: c };

    Round1Message { 
        a_commit: a_eval,
        b_commit: b_eval,
        c_commit: c_eval,
    }
}

// Takes a bunch of coefficients and extends the basis by 4x
fn extend_lagrange_basis(n: usize, evals: &[F], cofactor: &F) -> Vec<F> {
    let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let group_order = domain.size();
    let mut coeffs = (domain.ifft(evals)).into_iter().map(|x| x * cofactor).collect::<Vec<_>>();
    coeffs.extend(vec![F::zero(); group_order * 3]);
    let domain = GeneralEvaluationDomain::<F>::new(group_order * 4).unwrap();
    domain.fft(&coeffs)
}

fn round_2(witness: &Vec<F>, statement: &ProvingStatement, transcript: &mut Transcript) -> Round2Message {
    let gamma = transcript.gamma;
    let beta = transcript.beta;

    let n = statement.n as usize;
    let mut z_evals = vec![];
    z_evals.push(F::one());

    let rlc = |a, b| a + beta * b + gamma;
    let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let mut w = domain.group_gen();
    for i in 0..(n - 1) {
        // Root of unity +
        let coeff = rlc(witness[i], w) * 
            rlc(witness[n + i], F::one() * w) *
            rlc(witness[2 * n + i], F::from(2) * w) /
            rlc(witness[i], statement.permutation[i]) * 
            rlc(witness[n + i], statement.permutation[n + i]) *
            rlc(witness[2 * n + i], statement.permutation[2 * n + i]);
        z_evals.push(coeff);
        w *= domain.group_gen();
    }
    let z = domain.ifft(&z_evals);
    let z_eval = eval_trusted(&z, &statement);
    transcript.z = DensePolynomial { coeffs: z };
    transcript.z_evals = z_evals;

    return Round2Message { 
        z_commit: z_eval
    }
}

fn round_3(
    witness: &Vec<F>,
    statement: &ProvingStatement,
    public_inputs: &Vec<F>,
    transcript: &mut Transcript
) -> Round3Message {
    let n = statement.n as usize;
    let a = &witness[..n];
    let b = &witness[n..(2 * n)];
    let c = &witness[(2 * n)..(3 * n)];

    let fft_cofactor = &transcript.fft_cofactor;
    let beta = &transcript.beta;
    let gamma = &transcript.gamma;
    let alpha = &transcript.alpha;
    let z_evals = &transcript.z_evals;

    let domain = GeneralEvaluationDomain::<F>::new(n).unwrap();
    let group_order = domain.size();

    let mut quotient = vec![];
    // This is incorrect, you cannot compute the multiplication like this?
    // A way that you can do this is to 

    let a_big = extend_lagrange_basis(n, a, fft_cofactor);
    let b_big = extend_lagrange_basis(n, b, fft_cofactor);
    let c_big = extend_lagrange_basis(n, c, fft_cofactor);
    let qm_big = extend_lagrange_basis(n, &statement.qm, fft_cofactor);
    let ql_big = extend_lagrange_basis(n, &statement.ql, fft_cofactor);
    let qr_big = extend_lagrange_basis(n, &statement.qr, fft_cofactor);
    let qo_big = extend_lagrange_basis(n, &statement.qo, fft_cofactor);
    let qc_big = extend_lagrange_basis(n, &statement.qc, fft_cofactor);
    let pi_big = extend_lagrange_basis(n, public_inputs, fft_cofactor);
    let z_big = extend_lagrange_basis(n, z_evals, fft_cofactor);
    let s1_big = extend_lagrange_basis(n, &statement.s_sig1, fft_cofactor);
    let s2_big = extend_lagrange_basis(n, &statement.s_sig2, fft_cofactor);
    let s3_big = extend_lagrange_basis(n, &statement.s_sig3, fft_cofactor);

    println!("{:?}", qm_big.len());
    println!("{:?}", c_big.len());

    for i in 0..(group_order * 4) {
        let eval = a_big[i] * b_big[i] * qm_big[i]
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
    let L0_big = extend_lagrange_basis(n, &L0, fft_cofactor);

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

    let t_coeffs = quarter_domain.ifft(&t_eval);
    let t1 = domain.fft(&t_coeffs[..group_order]);
    let t2 = domain.fft(&t_coeffs[group_order..(group_order * 2)]);
    let t3 = domain.fft(&t_coeffs[(group_order * 2)..(group_order * 3)]);
    
    Round3Message {
        t_lo_commit: eval_trusted(&t1, statement),
        t_mid_commit: eval_trusted(&t2, statement),
        t_hi_commit: eval_trusted(&t3, statement)
    }
}

fn round_4(
    witness: &Vec<F>,
    statement: &ProvingStatement,
    transcript: &Transcript
) -> Round4Message {
    let n = statement.n as usize;
    let eval = GeneralEvaluationDomain::<F>::new(n as usize).unwrap();
    let a = eval.ifft(&witness[..n]);
    let b = eval.ifft(&witness[n..(2 * n)]);
    let c = eval.ifft(&witness[(2 * n)..(3 * n)]);
    let z = &transcript.z;
    let zeta = &transcript.zeta;
    let z_coeffs = eval.ifft(&z);

    let a_poly = DensePolynomial::from_coefficients_vec(a);
    let b_poly = DensePolynomial::from_coefficients_vec(b);
    let c_poly = DensePolynomial::from_coefficients_vec(c);
    let z_poly = DensePolynomial::from_coefficients_vec(z_coeffs);

    let a_hat = a_poly.evaluate(zeta);
    let b_hat = b_poly.evaluate(zeta);
    let c_hat = c_poly.evaluate(zeta);
    let zw_hat = c_poly.evaluate(&(zeta * &eval.group_gen()));
    let s_sig1_hat = statement.s_sig1.evaluate(zeta);
    let s_sig2_hat = statement.s_sig2.evaluate(zeta);
    let s_sig3_hat = statement.s_sig3.evaluate(zeta);

    Round4Message {
        a_hat,
        b_hat,
        c_hat,
        zw_hat,
        s_sig1_hat,
        s_sig2_hat,
        s_sig3_hat
    }
}

fn round_5(
    statement: &ProvingStatement,
    r4_msg: &Round4Message,
    transcript: &Transcript
) -> Round5Message {
    let a = &transcript.a;
    let b = &transcript.b;
    let c = &transcript.c;
    let t1 = &transcript.t1;
    let t2 = &transcript.t2;
    let t3 = &transcript.t3;
    let z = &transcript.z;
    let alpha = &transcript.alpha;
    let zeta = &transcript.zeta;
    let beta = &transcript.beta;
    let gamma = &transcript.gamma;
    let mu = &transcript.mu;

    // let rx = vec![];
    let domain = GeneralEvaluationDomain::<F>::new(statement.n as usize).unwrap();
    let group_order = domain.size();

    let mut L1 = vec![F::one()];
    L1.extend(&vec![F::zero(); group_order - 1]);
    let L1_coeffs = DensePolynomial::from_coefficients_vec(domain.ifft(&L1));

    let zh_eval = zeta.pow(vec![group_order as u64]) - F::one();

    let wrp = |x| DensePolynomial::from_coefficients_vec(vec![x]);

    let r = &statement.qm * (r4_msg.a_hat * r4_msg.b_hat)
        + &statement.ql * r4_msg.a_hat 
        + &statement.qr * r4_msg.b_hat 
        + &statement.qo * r4_msg.c_hat
        + statement.qc.clone()
        + z.mul(
            (r4_msg.a_hat + beta * zeta + gamma)
            * (r4_msg.b_hat + beta * zeta * F::from(2) + gamma)
            * (r4_msg.c_hat + beta * zeta * F::from(3) + gamma)
        ).sub(
            &(statement.s_sig3.mul(beta.clone()) + DensePolynomial::from_coefficients_vec(vec![gamma.clone() + r4_msg.c_hat])
            .mul((r4_msg.a_hat + beta * &r4_msg.s_sig1_hat + gamma) * (r4_msg.b_hat + beta + &r4_msg.s_sig2_hat + gamma) * r4_msg.zw_hat))
        ).mul(*alpha)
        + (z.sub(&DensePolynomial::from_coefficients_vec(vec![F::one()]))).mul(alpha * alpha * L1_coeffs.evaluate(zeta))
        .sub(&(t1 + &(t2.mul(zeta.pow(vec![group_order as u64])) + t3.mul(zeta.pow(vec![(group_order * 2) as u64])))));

    let W = &(
        &r + &(
        &(a - &wrp(r4_msg.a_hat)) * *mu +
        &(b - &wrp(r4_msg.b_hat)) * mu.pow(vec![2]) +
        &(c - &wrp(r4_msg.c_hat)) * mu.pow(vec![3]) +
        &(&statement.s_sig1 - &wrp(r4_msg.s_sig1_hat)) * mu.pow(vec![4]) +
        &(&statement.s_sig2 - &wrp(r4_msg.s_sig2_hat)) * mu.pow(vec![5]))
    ) / &(DensePolynomial::from_coefficients_vec(vec![-zeta.clone(), F::one()]));

    let W_zw = &(z - &wrp(r4_msg.zw_hat)) / & (DensePolynomial::from_coefficients_vec(vec![-(zeta * &domain.group_gen()), F::one()]));

    return Round5Message {
        W_commit: eval_trusted(&W.coeffs, statement),
        W_zw_commit: eval_trusted(&W_zw.coeffs, statement),
    }
}

macro_rules! timed_exec {
    ($msg:expr, $func:expr) => {
        {
            let start = Instant::now();
            let result = $func;
            let elapsed = start.elapsed();
            println!("{} took: {} ms", $msg, elapsed.as_millis());
            result
        }
    };
}


fn main() {
    // CHANGE THIS TO GET BETTER BENCHMARKS
    const K: u32 = 17;

    let mut transcript = Transcript::new();
    transcript.alpha = F::from(123);
    transcript.beta = F::from(12345);
    transcript.gamma = F::from(1234567);
    transcript.zeta = F::from(123456789);
    transcript.mu = F::from(1267891);
    transcript.fft_cofactor = F::from(12672221);

    let to_f = |x: Vec<u64>| x.into_iter().map(|x| F::from(x)).collect::<Vec<F>>();

    let circuit_size = 2_u64.pow(K) as usize;

    timed_exec!("Overall Execution", || {
        let statement = timed_exec!("Setup", setup(
            circuit_size as u64,
            to_f(vec![0; circuit_size]), // qm,
            to_f(vec![0; circuit_size]), // ql,
            to_f(vec![0; circuit_size]), // qr,
            to_f(vec![0; circuit_size]), // qo, 
            to_f(vec![0; circuit_size]), // qc
        ));
    
        let a = to_f(vec![2; circuit_size]);
        let b = to_f(vec![2; circuit_size]);
        let c = to_f(vec![4; circuit_size]);
        let public_inputs = to_f(vec![0; circuit_size]);
    
        let mut witness = a.clone();
        witness.extend(a);
        witness.extend(b);
        witness.extend(c);
        let r1_msg = timed_exec!("Round 1", round_1(&witness, &statement, &mut transcript));
        let r2_msg = timed_exec!("Round 2", round_2(&witness, &statement, &mut transcript));
        let r3_msg = timed_exec!("Round 3", round_3(&witness, &statement, &public_inputs, &mut transcript));
        let r4_msg = timed_exec!("Round 4", round_4(&witness, &statement, &mut transcript));
        let r5_msg = timed_exec!("Round 5", round_5(&statement, &r4_msg, &mut transcript));
    });
}
