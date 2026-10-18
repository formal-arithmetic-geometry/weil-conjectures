## What changed

The item module now assembles the telescope quasi-isomorphism, finite-dual K-flatness,
unit normalization, slice restriction, uniqueness, and coherence. Four strictly smaller
intermediate conclusions were added as separate modules and imported privately by the
item. The finite-dual term theorem is proved from the existing Hom-to-single isomorphism,
finite free tensor isomorphism, and bounded-above-flat K-flat theorem. The main theorem
has no `sorry`.

## Proved and sorry left

Proved `ringed_cech_koszul_dual_limit` and the helper uniqueness, transport, and coherence
lemmas in the item module. The following named intermediate theorems remain as explicit
stage-3 obligations:

- `ringedKoszul_colimit_cech` in `lem-weil-pbc-ringed-koszul-colimit-cech`;
- `ringedKoszulDual_flat_terms` in `lem-weil-pbc-ringed-koszul-dual-flat-terms`;
- `ringedKoszul_cech_local_model` in `lem-weil-pbc-ringed-koszul-cech-local-model`;
- `ringedCech_normalized_restriction` in `lem-weil-pbc-ringed-cech-normalized-restriction`.

## No longer needed

No proof-dependency node was removed. The original item imports remain where used by the
assembly; the four new modules are the only additional imports.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan describes the complete chain-level construction but the library had no
single declarations for the colimit calculation, finite-dual term analysis, normalized
single-site comparison, or restriction package. These are split off as the four named
conclusions above; the item theorem is proved by a real assembly from them.

## New nodes

The four node files are `lem-weil-pbc-ringed-cech-normalized-restriction`,
`lem-weil-pbc-ringed-koszul-cech-local-model`, `lem-weil-pbc-ringed-koszul-colimit-cech`,
and `lem-weil-pbc-ringed-koszul-dual-flat-terms`; they correspond one-to-one with the
four new intermediate modules and declarations listed above.

The proof-only imports for HomComplex, strict tower, K-injective products,
restriction exactness, and related modules are encapsulated by the four helper modules;
the existing public KFlatCoefficientUniverse interface is retained.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
