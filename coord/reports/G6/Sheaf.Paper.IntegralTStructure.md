## What changed

Proved all four original holes in `lean/Sheaf/Paper/IntegralTStructure.lean`, without changing any declaration signature, definition, visibility, or existing public import. The proof uses three proof-only imports: `Sheaf.Paper.PbcUniformCompleteTriangulated`, `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`, and `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`.

The existing uniform-category theorem supplies triangulatedness; the canonical-truncation membership theorem supplies Mathlib's induced-structure constructor. The stratified-perfect characterization supplies boundedness after converting stalkwise prime invertibility into global invertibility. Ambient vanishing characterizes the heart. The proved upstream comparisons for a t-exact inclusion give the natural truncation isomorphisms. Faithfulness proves shift linearity, and the truncation adjunction injectivity lemmas prove preservation of the original torsion exponent. The node proof and direct dependencies now record this implementation.

Validation: the complete module compiles through lcompile.py in 6.0 seconds with no warnings. The proof includes negative, zero and positive cutoffs without case restrictions; the heart argument covers every nonzero integer; torsion uses the original exponent and needs no flatness assumption. No new witness is chosen from an unproved existence theorem.

## Proved and sorry left

Closed 4 of the original 4 holes, all attached to node `prop-weil-pbc-integral-tstructure`:

- `AlgebraicGeometry.Scheme.pbcIntegralProperty_isTriangulated`.
- `AlgebraicGeometry.Scheme.pbcIntegralProperty_hasInducedTStructure`.
- `AlgebraicGeometry.Scheme.pbcIntegralShift_isLinear`.
- `AlgebraicGeometry.Scheme.pbc_integral_tstructure`.

Holes left in the item: zero. Holes added elsewhere: zero. Split-offs: zero. These are proofs from existing declarations; the membership, characterization and triangulation dependencies retain their own proof obligations. This delivery does not assert that the entire dependency closure is sorry-free.

## No longer needed

The three original public imports are used by the statements or definitions and remain. Compared with the current shared checkout, removed proof-only imports are `Sheaf.Paper.AdicCoefficientDatum`, `Sheaf.Paper.IntegralUniformCoefficient`, and `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`. The actual coefficient and scalar interfaces are already supplied by the retained public dependency chain; the broad heart/homology theory is unnecessary because the proof uses the proved Mathlib adjunction extensionality API and the more specific upstream SpectralObject comparisons. All three retained proof imports are used. No module is withdrawn.

The explicit standalone use of `lem-sf-derived-truncation-triangle` is unnecessary: Mathlib's HasInducedTStructure.mk' directly supplies the ambient canonical triangle. Its direct proof edge and obsolete tool approval are removed. The separate plan edges to `def-weil-derived-cohomology-sheaves`, `def-weil-pbc-adic-coefficient-datum`, and `def-weil-abstract-derived-category` are also unnecessary as proof steps: the published ambient t-structure, actual scalar action and membership interfaces already expose what this argument uses. Their statement-level role and all relevant public imports remain. No claim is made that these definition modules disappear from the targets' import closure.

The node `lem-weil-heart-short-exact-triangles` remains as the adjunction/uniqueness dependency; its facts are implemented using already proved Mathlib extensionality lemmas and upstream t-exact comparison isomorphisms. The upstream comparisons are a generic tool, not a replacement of a unit step; this item's unit `sk-rem-rest` has no realized statement or proof steps to bypass.

## Where the brief, the DAG or earlier work was wrong

The initial shared-file read raced with a checkout update; the assigned module subsequently appeared and was copied without altering the shared repository. No mathematical correction or consumer adaptation was necessary.

The published Lean theorem states boundedness, the heart, natural ambient comparisons and torsion preservation. The node's additional conditional tower description is supplied by the separately published `pbc_integral_truncations` through the existing public import; this delivery preserves that interface and does not change the theorem's signature or assert unrestricted reduction/truncation commutation.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
