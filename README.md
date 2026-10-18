# Aerie projections

Lean proofs of the structured projection guarantees used in *Aerie: Efficient Aggregation of Falcon Signatures*.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/quangvdao/aerie-projections.git
cd aerie-projections
lake exe cache get
lake build
```

The toolchain and Mathlib revision are pinned. The default build checks the Aerie proofs, their transitive axiom dependencies, and the specification constants. It succeeds only if these checks pass. The axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

## Main theorems

In [`CertifiedProjections/Aerie/Falcon.lean`](CertifiedProjections/Aerie/Falcon.lean), namespace `CertifiedProjections.Aerie`:

- `falcon512_projection_sound` and `falcon1024_projection_sound`: false acceptance probability at most 2⁻¹³⁶.
- `falcon512_projection_complete` and `falcon1024_projection_complete`: honest rejection probability at most 2⁻¹²⁹ + 2⁻¹⁴².

These results cover the supported padded batch geometries up to 65,536 records. Soundness assumes bounded public coefficients, centered signature coefficients `s2` bounded by 2047, and the rowwise norm identities modulo the proof field. The source is fixed before the independent projection randomness is sampled. The conclusions concern the integer norm and ring equations; the rest of Aerie's proof system is outside this development.

This repository contains only the Aerie import closure and its two validation modules, extracted from CertifiedProjections at `7f02baa9036cab0dffb2b6728d622d90ec701c5d`. It builds without that repository. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
