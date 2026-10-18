## What changed

Proved all four theorems in
`lean/Sheaf/AlgebraicGeometry/RelativeFrobeniusGeometricFiber.lean`, following their
existing proof docstrings. Added the proof-only import
`Mathlib.Algebra.CharP.CharAndCard` for `charP_of_card_eq_prime_pow`.
Every existing signature, public import, definition and docstring is unchanged.

`model_characteristic` transports the characteristic from the finite base field
through its map into global sections. `model_frobenius_over` uses extensionality
for maps into Spec, power preservation, and `FiniteField.pow_card`.
`relativeFrobenius_projections` uses the defining lift equations of `Over.pullback`.
`relativeFrobenius_affine` first identifies model Frobenius with Spec of
`FiniteField.frobeniusAlgHom` through global sections, then compares both
projections after `pullbackSpecIso`. The first tensor-factor equation reduces by
congruence; the second follows by evaluation of the tensor map on `1 ⊗ x`.
No new lemma modules or DAG nodes were needed, and the original route is unchanged.

Read Deligne, Weil II (1.1.14), p. 153 (PDF p. 18), and Stacks varieties.tex,
`definition-absolute-frobenius`, `lemma-frobenius-endomorphism-identity`, and
`definition-relative-frobenius`. Read all nine statement dependencies and their
recorded Lean declarations. The node has no separate proof dependencies and no unit.
Logged semantic search found `charP_of_card_eq_prime_pow`; logged source search
found that lemma and `pullbackSpecIso`. The Loogle query with a FiniteField prefix
was invalid because that lemma is in the root namespace; the semantic and source
searches resolved its correct name.

Validation: lcompile.py compiled the complete module without warnings in 6.6 s.
`#print axioms` for all four theorems and `relativeFrobenius` reports only
`propext`, `Classical.choice`, and `Quot.sound`.
The argument uses no nontriviality assumption on section rings or on A, so includes
the empty scheme and zero affine ring. The arbitrary Fintype on the finite base is
related to its specified cardinality using `Nat.card_eq_fintype_card`.

## Proved and sorry left

Closed 4 of 4 original holes, all belonging to
`def-weil-relative-frobenius-geometric-fiber`:

- `WeilConjectures.FiniteFieldDatum.model_characteristic`
- `WeilConjectures.FiniteFieldDatum.model_frobenius_over`
- `WeilConjectures.FiniteFieldDatum.relativeFrobenius_projections`
- `WeilConjectures.FiniteFieldDatum.relativeFrobenius_affine`

No sorry remains; no hole was added or split off. The definition
`WeilConjectures.FiniteFieldDatum.relativeFrobenius` is unchanged.

## No longer needed

None. No imports were removed, and no nodes or modules were pruned.
The existing absolute-Frobenius construction, finite-field power lemma and affine
fibre-product isomorphism are all used. No additional Frobenius well-definedness
module is needed: the published construction and the global-sections API suffice.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The definition node has empty proof/proof_deps;
the four existing declaration docstrings give the proof route completed here.
The bundled affine model needs an explicit local QuasiCompact instance, obtained
from the existing instance on its displayed Spec morphism. Rewrites involving the
bundled geometric fibre need `erw` to expose the same chosen pullback. These are
elaboration details and require no statement or definition repair.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
