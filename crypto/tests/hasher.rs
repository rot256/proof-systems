use mina_crypto::hasher::Hashable;
use mina_crypto::hasher::Hasher;
use mina_crypto::hasher::ROInput;
use mina_curves::pasta::Fp;
use o1_utils::FieldHelpers;
use serde::Deserialize;
use std::fs::File;
use std::path::PathBuf; // needed for ::new() sponge

//
// Helpers for test vectors
//

#[derive(Debug, Deserialize)]
struct TestVectors {
    test_vectors: Vec<TestVector>,
}

#[derive(Clone, Debug, Deserialize)]
struct TestVector {
    input: Vec<String>,
    output: String,
}

impl Hashable for TestVector {
    type D = ();

    fn to_roinput(self) -> ROInput {
        let mut roi = ROInput::new();
        // For hashing we only care about the input part
        for input in self.input {
            roi.append_field(Fp::from_hex(&input).expect("failed to deserialize field element"))
        }
        roi
    }

    fn domain_string(_: Option<Self>, _: &Self::D) -> Option<String> {
        None
    }
}

fn test_vectors(test_vector_file: &str, hasher: &mut dyn Hasher<TestVector>) {
    // read test vectors from given file
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../oracle/tests/test_vectors");
    path.push(&test_vector_file);
    println!("path = {:?}", path);
    let file = File::open(&path).expect("couldn't open test vector file");
    let test_vectors: TestVectors =
        serde_json::from_reader(file).expect("couldn't deserialize test vector file");

    // execute test vectors
    for test_vector in test_vectors.test_vectors {
        let expected_output =
            Fp::from_hex(&test_vector.output).expect("failed to deserialize field element");

        // hash & check against expect output
        let output = hasher.hash(test_vector);
        assert_eq!(output, expected_output);
    }
}

//
// Tests
//

#[test]
fn hasher_test_vectors_legacy() {
    let mut hasher = mina_crypto::hasher::create_legacy::<TestVector>(());
    test_vectors("legacy.json", &mut hasher);
}

#[test]
fn hasher_test_vectors_kimchi() {
    let mut hasher = mina_crypto::hasher::create_kimchi::<TestVector>(());
    test_vectors("kimchi.json", &mut hasher);
}
