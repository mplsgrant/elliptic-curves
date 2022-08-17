#![cfg_attr(feature = "std", doc = "```")]
#![cfg_attr(not(feature = "std"), doc = "```ignore")]

use crate::schnorr::signature::Signature as SSignature;
use crate::schnorr::{Signature, VerifyingKey};
use crate::{AffinePoint, FieldBytes, ProjectivePoint, Scalar, SecretKey, ORDER};
use core::ops::Neg;
use elliptic_curve::bigint::{Encoding, UInt};
use elliptic_curve::consts::{U113, U145, U64, U65, U66};
use elliptic_curve::generic_array::sequence::Concat;
use elliptic_curve::generic_array::typenum::{U32, U33};
use elliptic_curve::generic_array::{ArrayLength, GenericArray};
use elliptic_curve::group::prime::PrimeCurveAffine;
use elliptic_curve::group::GroupEncoding;
use elliptic_curve::ops::Reduce;
use elliptic_curve::subtle::{Choice, CtOption};
use elliptic_curve::Group;
use elliptic_curve::{bigint::U256, DecompressPoint};
use sha2::{Digest, Sha256};

#[derive(Debug, Eq, PartialEq)]
struct SecNonce {
    nonce: GenericArray<u8, U64>,
}

impl SecNonce {
    pub fn new(nonce: GenericArray<u8, U64>) -> Self {
        Self { nonce }
    }

    pub fn left_bytes(&mut self) -> GenericArray<u8, U32> {
        let mut left = GenericArray::default();
        let split = self.nonce.split_at(32);
        left.copy_from_slice(split.0);
        left
    }

    pub fn right_bytes(&self) -> GenericArray<u8, U33> {
        let mut right = GenericArray::default();
        let split = self.nonce.split_at(32);
        right.copy_from_slice(split.1);
        right
    }

    pub fn clear_nonce(&mut self) {
        let values = GenericArray::default();
        self.nonce = values;
    }
}

#[derive(Default, Debug, Eq, PartialEq, Clone, Copy)]
struct PubNonce {
    nonce: GenericArray<u8, U66>,
}

impl PubNonce {
    pub fn new(nonce: GenericArray<u8, U66>) -> Self {
        Self { nonce }
    }

    pub fn update_left(&mut self, left: GenericArray<u8, U33>) {
        self.nonce[0..33].copy_from_slice(&left);
    }

    pub fn update_right(&mut self, right: GenericArray<u8, U33>) {
        self.nonce[33..].copy_from_slice(&right);
    }

    pub fn left_bytes(&self) -> GenericArray<u8, U33> {
        let mut left = GenericArray::default();
        let split = self.nonce.split_at(32);
        left.copy_from_slice(split.0);
        left
    }

    pub fn right_bytes(&self) -> GenericArray<u8, U33> {
        let mut right = GenericArray::default();
        let split = self.nonce.split_at(32);
        right.copy_from_slice(split.1);
        right
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
struct Msg {
    // Using 32-bytes for now. Spec calls for variable length, but for the
    // moment, I can't be bothered to implement that without access to std
    // libraries.
    msg: GenericArray<u8, U32>,
}

impl Msg {
    pub fn new(msg: GenericArray<u8, U32>) -> Self {
        Self { msg }
    }
    pub fn len(&self) -> usize {
        self.msg.len()
    }
    pub fn to_bytes(&self) -> GenericArray<u8, U32> {
        self.msg.clone()
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
struct Tweak {
    bytes: GenericArray<u8, U32>,
}

impl Tweak {
    pub fn new(bytes: GenericArray<u8, U32>) -> Result<Self, elliptic_curve::Error> {
        if int_from_bytes(&bytes) >= ORDER {
            Err(elliptic_curve::Error)
        } else {
            Ok(Tweak { bytes })
        }
    }

    pub fn to_bytes(&self) -> GenericArray<u8, U32> {
        self.bytes
    }
}

/// Return a tagged hash
fn tagged_hash(tag: &[u8], msg: &[u8]) -> Sha256 {
    let tag_hash = Sha256::digest(tag);
    let mut digest = Sha256::new();
    digest.update(&tag_hash);
    digest.update(&tag_hash);
    digest.update(msg);
    digest
}

fn is_infinite(point: AffinePoint) -> Choice {
    point.is_identity()
}

// x(point) is obvious
// y(point) is obvious
// add(point, point) is obvious
// mul(point, point) is obvious

// bytes_from_int

fn lift_x(bytes: &FieldBytes) -> CtOption<AffinePoint> {
    AffinePoint::decompress(bytes, Choice::from(0))
}

// int_from_bytes
fn int_from_bytes(bytes: &[u8]) -> U256 {
    U256::from_be_slice(bytes)
}

fn bytes_from_point(point: AffinePoint) -> GenericArray<u8, U32> {
    point.x.to_bytes()
}

fn schnorr_verify(msg: &[u8; 32], verifying_key: &[u8], sig: &[u8]) -> bool {
    match (
        VerifyingKey::from_bytes(verifying_key),
        Signature::from_bytes(sig),
    ) {
        (Ok(pk), Ok(sig)) => pk.verify_prehashed(msg, &sig).is_ok(),
        _ => false,
    }
}

fn cbytes(point: AffinePoint) -> GenericArray<u8, U33> {
    let a = if point.y.is_even().unwrap_u8() == 1 {
        &[b'\x02']
    } else {
        &[b'\x03']
    };
    let mut result: GenericArray<u8, U33> = GenericArray::default();
    result[1..=33].copy_from_slice(bytes_from_point(point).as_slice());
    result[..=1].copy_from_slice(a);
    result
}

fn cbytes_extended(point: AffinePoint) -> GenericArray<u8, U33> {
    if point.is_identity().unwrap_u8() == 1 {
        let mut result: GenericArray<u8, U33> = GenericArray::default();
        result.copy_from_slice(&[0; 33]);
        result
    } else {
        cbytes(point)
    }
}

fn cpoint(x_bytes: &GenericArray<u8, U33>) -> CtOption<AffinePoint> {
    // TODO: Does this crate offer a 33-byte compressed serialization format?
    // Shall I make such a struct?
    let x = FieldBytes::from_slice(&x_bytes[1..33]);
    let point = lift_x(x);
    if point.is_none().unwrap_u8() == 1 {
        CtOption::new(AffinePoint::default(), Choice::from(0))
    } else if x_bytes[0] == 2 {
        CtOption::new(point.unwrap(), Choice::from(1))
    } else if x_bytes[0] == 3 {
        let point = point_negate(point.unwrap());
        CtOption::new(point, Choice::from(1))
    } else {
        panic!("PANIC!")
    }
}

fn point_negate(point: AffinePoint) -> AffinePoint {
    point.neg()
}

fn cpoint_extended(x_bytes: &GenericArray<u8, U33>) -> CtOption<AffinePoint> {
    let zero: &GenericArray<u8, U33> = GenericArray::from_slice(&[0u8; 33]);
    if x_bytes == zero {
        CtOption::new(AffinePoint::default(), Choice::from(0))
    } else {
        cpoint(x_bytes)
    }
}

struct KeyGenContext {
    pub q: AffinePoint, // pk
    pub tacc: Scalar,
    pub gacc: Scalar,
}

fn get_pk(ctx: KeyGenContext) -> AffinePoint {
    let bytes = bytes_from_point(ctx.q);
    let field_bytes = FieldBytes::from_slice(&bytes);
    AffinePoint::from_bytes(field_bytes).unwrap()
}

fn key_agg<N: ArrayLength<AffinePoint>>(points: &GenericArray<AffinePoint, N>) -> KeyGenContext {
    let pk2 = get_second_key(points);
    let mut q = AffinePoint::identity().to_curve();
    for pk in points.iter() {
        let a_i = key_agg_coef_internal(points, pk, &pk2);
        let foo: ProjectivePoint = pk.to_curve();
        let bar = Scalar::from_uint_reduced(a_i);
        let baz = foo * bar;
        q += baz;
    }
    assert_ne!(q.is_identity().unwrap_u8(), 1);

    let q = q.to_affine();
    let gacc = Scalar::from_uint_reduced(UInt::<4>::from_u8(1));
    let tacc = Scalar::from_uint_reduced(UInt::<4>::from_u8(0));

    KeyGenContext { q, tacc, gacc }
}

fn hash_keys<N: ArrayLength<AffinePoint>>(
    points: &GenericArray<AffinePoint, N>,
) -> GenericArray<u8, U32> {
    let tag_hash = Sha256::digest(b"KeyAgg list");
    let mut digest = Sha256::new();
    digest.update(&tag_hash);
    digest.update(&tag_hash);
    for i in points {
        let data = i.to_bytes();
        digest.update(data)
    }
    digest.finalize()
}

fn get_second_key<N: ArrayLength<AffinePoint>>(keys: &GenericArray<AffinePoint, N>) -> AffinePoint {
    let u = keys.len();
    for j in 1..u {
        if keys[j] != keys[0] {
            return keys[j];
        }
    }
    keys[0]
}

fn key_agg_coef<N: ArrayLength<AffinePoint>>(
    points: &GenericArray<AffinePoint, N>,
    pk: &AffinePoint,
) -> UInt<4> {
    let pk2 = get_second_key(points);
    key_agg_coef_internal(points, pk, &pk2)
}

fn key_agg_coef_internal<N: ArrayLength<AffinePoint>>(
    points: &GenericArray<AffinePoint, N>,
    pk: &AffinePoint,
    pk2: &AffinePoint,
) -> UInt<4> {
    let l = hash_keys(points);
    if pk == pk2 {
        let one = UInt::<4>::from_u8(1);
        return one;
    }
    let mut hasher = tagged_hash(b"KeyAgg coefficient", l.as_slice());
    hasher.update(pk.to_bytes());
    let bytes = hasher.finalize();
    let coef = int_from_bytes(bytes.as_slice());
    coef.add_mod(&UInt::from_u8(0), &ORDER)
}

fn apply_tweak(keygen_ctx: KeyGenContext, tweak: &Tweak, is_xonly: bool) -> KeyGenContext {
    let q = keygen_ctx.q;
    let gacc = keygen_ctx.gacc;
    let tacc = keygen_ctx.tacc;
    let mut g = Scalar::ONE;
    if is_xonly && q.y.is_even().unwrap_u8() == 1 {
        let n = Scalar::from_bytes_unchecked(&ORDER.to_be_bytes());
        g = n - Scalar::ONE;
    }

    let tweak = tweak.to_bytes();
    let mut fitted_tweak = [0u8; 32];
    for (i, elem) in fitted_tweak.iter_mut().enumerate() {
        *elem = tweak[i];
    }
    let t = Scalar::from_bytes_unchecked(&fitted_tweak);

    let generator = AffinePoint::generator();

    let q_and_g = q * g;
    let gen_and_t = generator * t;
    let q = q_and_g + gen_and_t;
    let q = q.to_affine();

    assert_eq!(q.is_identity().unwrap_u8(), 0); // TODO Do proper error checking.

    let gacc = g * gacc;
    let tacc = t + g * tacc;

    KeyGenContext { q, tacc, gacc }
}

fn bytes_xor<N: ArrayLength<u8>>(
    left: GenericArray<u8, N>,
    right: GenericArray<u8, N>,
) -> GenericArray<u8, N> {
    right.iter().zip(left).map(|(x, y)| x ^ y).collect()
}

fn take_padded_1_bytes(bytes: &[u8]) -> [u8; 1] {
    let mut result = [0u8; 1];

    result[0] = *bytes
        .last()
        .expect("The byte field should have at lease one element.");
    result
}

fn take_padded_4_bytes(bytes: &[u8]) -> [u8; 4] {
    let mut result = [0u8; 4];
    result[4 - bytes.len()..].copy_from_slice(bytes);
    result
}

fn nonce_hash<RN: ArrayLength<u8>, XN: ArrayLength<u8>>(
    rand: &GenericArray<u8, RN>,
    aggpk: &Option<AffinePoint>,
    i: u32,
    msg: &Option<Msg>,
    extra_in: &Option<GenericArray<u8, XN>>,
) -> U256 {
    let mut hasher = Sha256::new();
    let tag = b"MuSig/nonce";

    hasher.update(tag);
    hasher.update(tag);

    hasher.update(rand.as_slice());

    if let Some(aggpk) = aggpk {
        hasher.update(take_padded_1_bytes(&aggpk.to_bytes().len().to_be_bytes()));
        hasher.update(aggpk.to_bytes());
    } else {
        hasher.update(&[0]); // Just the length.
    };

    if let Some(msg) = msg {
        hasher.update(take_padded_1_bytes(&msg.len().to_be_bytes()));
        hasher.update(&msg.to_bytes());
    } else {
        hasher.update(&[0]);
    };

    if let Some(extra_in) = extra_in {
        hasher.update(take_padded_4_bytes(&extra_in.len().to_be_bytes()));
        hasher.update(extra_in);
    } else {
        hasher.update(&[0]);
    };

    hasher.update(take_padded_1_bytes(&i.to_be_bytes()));
    let bytes = hasher.finalize();
    int_from_bytes(&bytes)
}

fn nonce_gen_internal<RN: ArrayLength<u8>, XN: ArrayLength<u8>>(
    rand: GenericArray<u8, RN>,
    sk: Option<SecretKey>,
    aggpk: Option<AffinePoint>,
    msg: Option<Msg>,
    extra_in: Option<GenericArray<u8, XN>>,
) -> (PubNonce, SecNonce) {
    let rand = if let Some(sk) = sk {
        let hash = tagged_hash(b"MuSig/aux", &rand).finalize();
        let sk = sk.to_be_bytes();
        let new_rand: GenericArray<u8, RN> = hash.iter().zip(sk).map(|(x, y)| x ^ y).collect(); // bytes_xor
        new_rand
    } else {
        rand
    };

    let k_1 = nonce_hash(&rand, &aggpk, 0, &msg, &extra_in);
    let k_2 = nonce_hash(&rand, &aggpk, 1, &msg, &extra_in);
    assert_ne!(k_1, UInt::from_u8(0));
    assert_ne!(k_2, UInt::from_u8(0));

    let k_1 = Scalar::from_bytes_unchecked(&k_1.to_be_bytes());
    let k_2 = Scalar::from_bytes_unchecked(&k_2.to_be_bytes());

    let r_1 = AffinePoint::generator() * k_1;
    let r_2 = AffinePoint::generator() * k_2;
    assert_ne!(!r_1.is_identity().unwrap_u8(), 1);
    assert_ne!(!r_2.is_identity().unwrap_u8(), 1);

    let r_1: GenericArray<u8, U33> = cbytes(r_1.to_affine());
    let r_2: GenericArray<u8, U33> = cbytes(r_2.to_affine());

    let pubnonce: GenericArray<u8, U66> = r_1.concat(r_2);
    let secnonce: GenericArray<u8, U64> = k_1.to_bytes().concat(k_2.to_bytes());

    let pubnonce = PubNonce::new(pubnonce);
    let secnonce = SecNonce::new(secnonce);

    (pubnonce, secnonce)
}

fn nonce_gen<XN: ArrayLength<u8>>(
    sk: Option<SecretKey>,
    aggpk: Option<AffinePoint>,
    msg: Option<Msg>,
    extra_in: Option<GenericArray<u8, XN>>,
) -> (PubNonce, SecNonce) {
    let rand = b"TEMPORARY VALUE THAT SHOULD BE SECRET...........................";
    let rand: GenericArray<u8, U64> = *GenericArray::from_slice(rand);
    nonce_gen_internal(rand, sk, aggpk, msg, extra_in)
}

fn nonce_agg<N: ArrayLength<PubNonce>>(pubnonces: &GenericArray<PubNonce, N>) -> PubNonce {
    let u = pubnonces.len();
    let mut aggnonce = PubNonce::default();
    for i in 0..2 {
        let mut r_i = AffinePoint::identity().to_curve();

        for j in 0..u {
            let r_ij = if i == 0 {
                pubnonces[j].left_bytes()
            } else {
                pubnonces[j].right_bytes()
            };
            let r_ij = cpoint(&r_ij).unwrap();
            let r_ij = r_ij.to_curve();
            r_i += r_ij;
        }

        if i == 0 {
            let foo = cbytes_extended(r_i.to_affine());
            aggnonce.update_left(foo)
        } else {
            let foo = cbytes_extended(r_i.to_affine());
            aggnonce.update_right(foo)
        }
    }

    aggnonce
}

struct SessionContext<AN: ArrayLength<AffinePoint>, TN: ArrayLength<Tweak>, BN: ArrayLength<bool>> {
    pub aggnonce: PubNonce,
    pub pubkeys: GenericArray<AffinePoint, AN>,
    pub tweaks: GenericArray<Tweak, TN>,
    pub is_xonly: GenericArray<bool, BN>,
    pub msg: Msg,
}

impl<AN, TN, BN> SessionContext<AN, TN, BN>
where
    AN: ArrayLength<AffinePoint>,
    TN: ArrayLength<Tweak>,
    BN: ArrayLength<bool>,
{
    pub fn get_session_values(&self) -> SessionValues {
        let kg_ctx = key_agg_and_tweak::<AN, TN, BN>(&self.pubkeys, &self.tweaks, &self.is_xonly);

        let mut bytes: GenericArray<u8, U145> = GenericArray::default();
        let tag = b"MuSig/noncecoef"; // 15
        let an = self.aggnonce.nonce.as_slice(); // 66
        let point = bytes_from_point(kg_ctx.q); // 32
        bytes[0..15].copy_from_slice(tag);
        bytes[15..81].copy_from_slice(an);
        bytes[81..113].copy_from_slice(point.as_slice());
        bytes[113..145].copy_from_slice(&self.msg.to_bytes());

        let b = int_from_bytes(&bytes);
        let b = Scalar::from_uint_reduced(b); // mod n

        let r_1 = cpoint_extended(&self.aggnonce.left_bytes()).unwrap();
        let r_2 = cpoint_extended(&self.aggnonce.right_bytes()).unwrap(); // TODO Implement error

        let r = r_1.to_curve() + r_2 * b;
        let r = if r.is_identity().unwrap_u8() == 1 {
            AffinePoint::generator().to_curve()
        } else {
            r
        };

        let mut bytes: GenericArray<u8, U113> = GenericArray::default();
        let tag = b"BIP0340/challenge"; // 17
        let r_bytes = bytes_from_point(r.to_affine()); // 32
        let q_bytes = bytes_from_point(kg_ctx.q); // 32
        bytes[0..17].copy_from_slice(tag);
        bytes[17..49].copy_from_slice(&r_bytes);
        bytes[49..81].copy_from_slice(&q_bytes);
        bytes[81..113].copy_from_slice(&self.msg.to_bytes());

        let e = int_from_bytes(&bytes);
        let e = Scalar::from_uint_reduced(e);

        SessionValues {
            q: kg_ctx.q,
            gacc: kg_ctx.gacc,
            tacc: kg_ctx.tacc,
            b,
            r,
            e,
        }
    }

    pub fn get_session_key_agg_coeff(&self, point: AffinePoint) -> UInt<4> {
        // TODO: Make this use Scalar instead of UInt.
        key_agg_coef(&self.pubkeys, &point)
    }
}

struct SessionValues {
    pub q: AffinePoint,
    pub gacc: Scalar,
    pub tacc: Scalar,
    pub b: Scalar,
    pub r: ProjectivePoint,
    pub e: Scalar,
}

fn key_agg_and_tweak<
    AN: ArrayLength<AffinePoint>,
    TN: ArrayLength<Tweak>,
    BN: ArrayLength<bool>,
>(
    pubkeys: &GenericArray<AffinePoint, AN>,
    tweaks: &GenericArray<Tweak, TN>,
    is_xonly: &GenericArray<bool, BN>,
) -> KeyGenContext {
    let mut keygen_ctx = key_agg(&pubkeys);
    for i in 0..tweaks.len() {
        keygen_ctx = apply_tweak(keygen_ctx, &tweaks[i], is_xonly[i]);
    }

    keygen_ctx
}

fn sign<AN: ArrayLength<AffinePoint>, TN: ArrayLength<Tweak>, BN: ArrayLength<bool>>(
    mut secnonce: SecNonce,
    sk: SecretKey,
    session_ctx: SessionContext<AN, TN, BN>,
) -> Scalar {
    let n = Scalar::from_bytes_unchecked(&ORDER.to_be_bytes());

    let session_values = session_ctx.get_session_values();
    let q = session_values.q;
    let gacc = session_values.gacc;
    let b = session_values.b;
    let r = session_values.r;
    let e = session_values.e;

    let k_1_ = secnonce.left_bytes();
    let k_2_ = secnonce.right_bytes();
    secnonce.clear_nonce();

    let k_1_ = int_from_bytes(&k_1_);
    let k_2_ = int_from_bytes(&k_2_);

    let k_1_ = Scalar::from_uint_reduced(k_1_);
    let k_2_ = Scalar::from_uint_reduced(k_2_);

    let r_has_even_y = r.to_affine().y.is_even().unwrap_u8() == 1;
    let k_1 = if r_has_even_y { k_1_ } else { n - k_1_ };
    let k_2 = if r_has_even_y { k_2_ } else { n - k_2_ };

    let d = sk;

    let p = d.public_key();

    let a = session_ctx.get_session_key_agg_coeff(*p.as_affine());
    let a = Scalar::from_uint_reduced(a);

    let gp = if p.as_affine().y.is_even().unwrap_u8() == 1 {
        Scalar::ONE
    } else {
        n - Scalar::ONE
    };
    let g = if q.y.is_even().unwrap_u8() == 1 {
        Scalar::ONE
    } else {
        n - Scalar::ONE
    };

    let d = g * gacc * gp * d.to_nonzero_scalar().as_ref(); // Scalars are mod n.

    let s = k_1 + b * k_2 + e * a * d;

    let r_1_ = AffinePoint::generator().to_curve() * k_1_;
    let r_2_ = AffinePoint::generator().to_curve() * k_2_;

    let left = cbytes(r_1_.to_affine());
    let right = cbytes(r_2_.to_affine());
    let mut pubnonce = PubNonce::default();
    pubnonce.update_left(left);
    pubnonce.update_right(right);

    // Optional correctness check. The result of signing should pass signature verification.
    assert!(partial_sig_verify_internal(
        s,
        pubnonce,
        *p.as_affine(),
        session_ctx
    ));

    s
}

fn partial_sig_verify<
    PN: ArrayLength<PubNonce>,
    AN: ArrayLength<AffinePoint>,
    TN: ArrayLength<Tweak>,
    BN: ArrayLength<bool>,
>(
    psig: Scalar,
    pubnonces: GenericArray<PubNonce, PN>,
    pubkeys: GenericArray<AffinePoint, AN>,
    tweaks: GenericArray<Tweak, TN>,
    is_xonly: GenericArray<bool, BN>,
    msg: Msg,
    i: usize,
) -> bool {
    let aggnonce = nonce_agg(&pubnonces);
    let session_ctx = SessionContext {
        aggnonce,
        pubkeys: pubkeys.clone(),
        tweaks,
        is_xonly,
        msg,
    };
    //     return partial_sig_verify_internal(psig, pubnonces[i], pubkeys[i], session_ctx)
    partial_sig_verify_internal(psig, pubnonces[i], pubkeys[i], session_ctx)
}

fn partial_sig_verify_internal<
    AN: ArrayLength<AffinePoint>,
    TN: ArrayLength<Tweak>,
    BN: ArrayLength<bool>,
>(
    psig: Scalar,
    pubnonce: PubNonce,
    pk_: AffinePoint,
    session_ctx: SessionContext<AN, TN, BN>,
) -> bool {
    let n = Scalar::from_bytes_unchecked(&ORDER.to_be_bytes());

    let s = psig;

    let session_values = session_ctx.get_session_values();
    let q = session_values.q;
    let gacc = session_values.gacc;
    let b = session_values.b;
    let r = session_values.r;
    let e = session_values.e;

    let r_1_ = cpoint(&pubnonce.left_bytes()).unwrap();
    let r_2_ = cpoint(&pubnonce.right_bytes()).unwrap();
    let r_b = r_1_.to_curve() + r_2_.to_curve() * b;
    let r_a = if r.to_affine().y.is_even().unwrap_u8() == 1 {
        r_b
    } else {
        point_negate(r_b.to_affine()).to_curve()
    };

    let g = if q.y.is_even().unwrap_u8() == 1 {
        Scalar::ONE
    } else {
        n - Scalar::ONE
    };

    let g_ = g * gacc;
    let p = pk_.to_curve() * g_;
    if p.is_identity().unwrap_u8() == 1 {
        return false;
    }
    let a = session_ctx.get_session_key_agg_coeff(p.to_affine());
    let a = Scalar::from_uint_reduced(a);

    let left = AffinePoint::identity() * s;
    let right = r_a + p * (e * a);

    left == right
}

fn partial_sig_agg<
    SN: ArrayLength<Scalar>,
    AN: ArrayLength<AffinePoint>,
    TN: ArrayLength<Tweak>,
    BN: ArrayLength<bool>,
>(
    psigs: GenericArray<Scalar, SN>,
    session_ctx: SessionContext<AN, TN, BN>,
) -> Signature {
    let n = Scalar::from_bytes_unchecked(&ORDER.to_be_bytes());

    let session_values = session_ctx.get_session_values();
    let q = session_values.q;
    let tacc = session_values.tacc;
    let r = session_values.r;
    let e = session_values.e;

    let mut s = Scalar::ZERO;

    for i in 0..psigs.len() {
        s += psigs[i];
    }

    let g = if q.y.is_even().unwrap_u8() == 1 {
        Scalar::ONE
    } else {
        n - Scalar::ONE
    };

    s += e * g * tacc;

    let nonce: GenericArray<u8, U65> = r.to_bytes().concat(s.to_bytes());

    Signature::from_bytes(&nonce[1..]).unwrap() // This will likely blow up b/c of the 65 byte issue in the nonce??
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use super::{get_pk, key_agg, lift_x};
    use crate::{AffinePoint, FieldBytes, PublicKey, Scalar};
    use elliptic_curve::consts::U6;
    use elliptic_curve::generic_array::{arr, GenericArray};
    use elliptic_curve::group::GroupEncoding;
    use elliptic_curve::PrimeField;
    use hex_literal::hex;

    #[test]
    fn key_agg_vectors() {
        // https://github.com/jonasnick/bips/blob/168699e3ec54a99320a70055f20e8e87baf2fe75/bip-musig2/key_agg_vectors.json#L1

        let mut pubkeys: [[u8; 32]; 6];
        pubkeys[0] = hex!("F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9");
        pubkeys[1] = hex!("DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659");
        pubkeys[2] = hex!("3590A94E768F8E1815C2F24B4D80A8E3149316C3518CE7B7AD338368D038CA66");
        pubkeys[3] = hex!("0000000000000000000000000000000000000000000000000000000000000005");
        pubkeys[4] = hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30");
        pubkeys[5] = hex!("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798");

        let mut tweaks: [[u8; 32]; 2];

        tweaks[0] = hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");
        tweaks[1] = hex!("11626F7DEBE62FBC840BB15C85B6F8C77D0B48DA3D2C0EB4A73B2099CB65056C");

        let mut points: [AffinePoint; 6];
        for (i, elem) in pubkeys.iter().enumerate() {
            let field_bytes = FieldBytes::from_slice(elem);
            let point = lift_x(field_bytes).unwrap();
            points[i] = point;
        }

        // valid test cases
        // "key_indices": [0, 1, 2],
        let select_points = arr!(AffinePoint; points[0], points[1], points[2]);
        let ctx = key_agg(&select_points);
        let pk = get_pk(ctx);
        let expected = hex!("E5830140512195D74C8307E39637CBE5FB730EBEAB80EC514CF88A877CEEEE0B");
    }

    #[test]
    fn it_works() {
        let a = hex!("97AC833ADCB1AFA42EBF9E0725616F3C9A0D5B614F6FE283CEAAA37A8FFAF406");
        let a = FieldBytes::from_slice(&a);
        let a = Scalar::from_repr(*a).unwrap();

        assert_eq!(1, 0);
    }
}
