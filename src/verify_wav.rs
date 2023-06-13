use crate::{
  commitments::poseidon_commit::{self, P128Pow5T3Gen},
  model::ModelCircuit,
  utils::{
    loader::load_config_msgpack,
    proving_kzg::{verify_circuit_kzg, verify_kzg},
    div_ceil,
  },
};

use std::{
  cmp::{max, min},
  io::{BufReader, Write, Cursor},
  time::Instant,
};

use halo2_proofs::{
  dev::MockProver,
  halo2curves::{
    bn256::{Bn256, Fq, Fq2, Fr, G1Affine, G2Affine},
    ff::PrimeField,
  },
  plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, VerifyingKey},
  poly::{
    commitment::{Params, ParamsProver},
    kzg::{
      commitment::{KZGCommitmentScheme, ParamsKZG},
      multiopen::{ProverSHPLONK, VerifierSHPLONK},
      strategy::SingleStrategy,
    },
  },
  transcript::{
    Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
  },
  SerdeFormat,
};
use halo2_gadgets::poseidon::{
  primitives::{ConstantLength, Domain, Hash},
  PaddedWord,
};

pub type PoseidonHasher =
  Hash<Fr, P128Pow5T3Gen<Fr, 0>, ConstantLength<{ poseidon_commit::L }>, 3, 2>;

pub fn get_exponents(num_bits_per_elem: usize, num_exponents: usize) -> Vec<Fr> {
  let mul_val = Fr::from(1 << num_bits_per_elem);
  let mut exponents = vec![Fr::one()];
  for _ in 1..num_exponents {
    exponents.push(exponents[exponents.len() - 1] * mul_val);
  }
  exponents
}

pub fn verify(vk: String, proof: String, public_vals: &[String], config: String) {
  let config_buf = hex::decode(config).unwrap();
  let config = rmp_serde::from_slice(&config_buf).unwrap();
  ModelCircuit::<Fr>::generate_from_msgpack(config, false);

  let vk = VerifyingKey::read::<BufReader<_>, ModelCircuit<Fr>>(
    &mut BufReader::new(hex::decode(&vk).unwrap().as_slice()),
    SerdeFormat::RawBytes,
    (),
  )
  .unwrap();
  println!("Loaded vkey");

  let proof = hex::decode(proof).unwrap();

  let public_vals: Vec<Fr> = public_vals
    .iter()
    .map(|x| Fr::from_str_vartime(x).unwrap())
    .collect();

  let params = ParamsKZG::<Bn256> {
    k: 24,
    n: 1 << 24,
    g: vec![G1Affine::generator()],
    g_lagrange: vec![],
    s_g2: G2Affine {
      x: Fq2::new(
        Fq::from_str_vartime(
          "17109015867118572030745779324212191698736396241608212876854183006212164292849",
        )
        .unwrap(),
        Fq::from_str_vartime(
          "10938796003451079337728171122795908661206257899267762973177153171611833735690",
        )
        .unwrap(),
      ),
      y: Fq2::new(
        Fq::from_str_vartime(
          "5207198165565673371403386229903402585220628358261245511764422372679613157540",
        )
        .unwrap(),
        Fq::from_str_vartime(
          "14794195211544794432532285509939829643330163063517964588789563791156406265496",
        )
        .unwrap(),
      ),
    },
    g2: G2Affine {
      x: Fq2::new(
        Fq::from_str_vartime(
          "10857046999023057135944570762232829481370756359578518086990519993285655852781",
        )
        .unwrap(),
        Fq::from_str_vartime(
          "11559732032986387107991004021392285783925812861821192530917403151452391805634",
        )
        .unwrap(),
      ),
      y: Fq2::new(
        Fq::from_str_vartime(
          "8495653923123431417604973247489272438418190587263600148770280649306958101930",
        )
        .unwrap(),
        Fq::from_str_vartime(
          "4082367875863433681332203403145435568316851327593401208105741076214120093531",
        )
        .unwrap(),
      ),
    },
  };

  let strategy = SingleStrategy::new(&params);

  let transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
  println!("Loaded configuration");
  println!("public_vals: {:?}", public_vals);
  verify_kzg(&params, &vk, strategy, &public_vals, transcript);
}

pub fn hash_poseidon(wav_str: String) -> String {
  let (_header, data) = wav::read(&mut Cursor::new(hex::decode(wav_str).unwrap())).unwrap();
  let data = match data {
    wav::BitDepth::Sixteen(data) => data,
    _ => panic!("Unsupported bit depth"),
  };
  let data: Vec<i64> = data.iter().map(|x| *x as i64).collect();
  let to_field = |x: i64| {
    let bias = 1 << 31;
    let x_pos = x + bias;
    Fr::from(x_pos as u64) - Fr::from(bias as u64)
  };

  let data: Vec<Fr> = data.iter().map(|x| *x as i64).map(to_field).collect();

  let num_packed_per_row = 1;
  let num_elem_per_packed = 9;
  let num_bits_per_elem = 16;
  let shift_val = Fr::from(1 << (num_bits_per_elem - 1));

  let zero = Fr::zero();

  let pack_row = |elems: &[Fr]| -> Vec<Fr> {
    let exponents = get_exponents(num_bits_per_elem, num_elem_per_packed);
    let mut packed = vec![];
    for i in 0..num_packed_per_row {
      let val_offset = i * num_elem_per_packed;
      let col_offset = i * (num_elem_per_packed + 1);

      let mut vals = elems[val_offset..min(val_offset + num_elem_per_packed, elems.len())]
        .iter()
        .cloned()
        .collect::<Vec<_>>();

      let zero_copied = (elems.len()..num_elem_per_packed)
        .map(|i| zero)
        .collect::<Vec<_>>();
      vals.extend(zero_copied);

      let res = vals
        .iter()
        .zip(exponents.iter())
        .fold(Fr::zero(), |acc, (inp, exp)| {
          let res = acc + (*inp + shift_val) * exp;
          res
        });

      packed.push(res);
    }
    packed
  };

  let pack = |elems: &[Fr]| -> Vec<Fr> {
    let mut packed = vec![];
    let num_elems_per_row = num_packed_per_row * num_elem_per_packed;
    for i in 0..(div_ceil(elems.len(), num_elems_per_row)) {
      let row =
        elems[i * num_elems_per_row..min((i + 1) * num_elems_per_row, elems.len())].to_vec();
      let row_packed = pack_row(&row);
      packed.extend(row_packed);
    }
    packed
  };

  println!("hashing");
  let mut hasher = PoseidonHasher::init();
  let packed_data = pack(&data);
  let mut new_vals = packed_data
    .iter()
    .map(|x| x.clone())
    .chain(vec![Fr::zero()])
    .collect::<Vec<_>>();
  while new_vals.len() % poseidon_commit::L != 0 {
    new_vals.push(Fr::zero());
  }
  for (_, value) in new_vals
    .into_iter()
    .chain(<ConstantLength<{ poseidon_commit::L }> as Domain<
      Fr,
      { poseidon_commit::RATE },
    >>::padding(poseidon_commit::L))
    .enumerate()
  {
    hasher.sponge.absorb(value);
  }
  let outp = hasher.sponge.finish_absorbing().squeeze();

  format!("{:?}", outp)
}
