## What changed

Implemented `AlgebraicGeometry.Scheme.finiteRootSiteComparison` in
`Sheaf.AlgebraicGeometry.FiniteRootSiteComparison` using the existing Cartier root
isomorphism. The public definitions, full specification, and theorem signature are
unchanged. All added constructions and proof helpers are private.

The tensor comparison is constructed explicitly through the Hom equivalences for
sheafification and extension/restriction of scalars. Precomposition with it is
bijective on Hom sets, proving invertibility. The scheme arrow is the transpose of
the recorded root projection map through the same scalar Hom equivalence. Generator
calculations prove normalization and scheme compatibility. Canonical adjunction
mates and fibre-product projection equations give identity and composition; kernel
inclusions and scalar Hom equivalences give exponent-change compatibility.

Updated the item's DAG proof, proof dependencies, and proof origin to describe this
route. It preserves the vector-bundle-purity unit route. The existing Cartier root
comparison lemma is now explicitly recorded as a proof dependency; it was already
used in the item's fixed root isomorphism and public imports. Its dependency closure
does not reach this item. No source-library file is modified.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.finiteRootSiteComparison` (one hole closed).
No holes added or split off. No `sorry` remains in the delivered module.
All twelve clauses of the original specification are retained, including generalized
unit restrictions, every scheme map, the canonical identity/composition comparisons,
and exponent one, zero coefficients, and empty schemes.

Validation: the full file compiled successfully on the project server in 32.7 seconds.
The diagnostic simplifier was replaced by its exact suggested `simp only` list.
Public definitions, the full specification and the theorem signature were compared
with the original and are unchanged. The module contains zero holes and all lines
meet the 100-character limit. Delivery reruns compilation and preflight.

## No longer needed

Removed the five private proof imports:
`Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`,
`Sheaf.Paper.RingedTopoiInverseImageTensorComparison`,
`Sheaf.Paper.ComparisonPullbackExact`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`, and
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
All original public imports are retained to preserve the public import interface.
The section-comparison import
`Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections` is retained because
preflight records it as a unit-route module. The direct kernel calculation in this
proof specializes that section identification without changing any unit statement
or proof step.

The proof uses the actual scalar-extension adjunctions rather than the general
ringed-topos inverse-image tensor theorem. Its direct proof route no longer needs
`def-weil-pbc-algebraic-inverse-image`,
`lem-weil-pbc-algebraic-inverse-image-tensor-comparison`,
`lem-sf-comparison-pullback-exact`,
`prop-weil-pbc-proetale-constant-ring-map`, or
`lem-pc-sites-sheaf-tensor-bilinear-universal`.

The existing Cartier kernel isomorphism and evaluated kernel descriptions replace
the direct use of `lem-cbc-comparison-pullback-sections`. The automatic `ZMod` linearity
of additive homomorphisms replaces the direct use of
`lem-pur-torsion-sheaf-constant-module`. Constant sheaves remain in the definitions;
`def-weil-pbc-constant-sheaf` is retained as a statement dependency rather than as a
separate proof step. The etale direct-image definition remains available through
the retained comparison interfaces.

No module is withdrawn. Some of these results remain transitively imported by
unchanged public dependencies; this report does not assert they are globally unused.
No adopted source declaration or proof is removed.

## Where the brief, the DAG or earlier work was wrong

The planned ringed tensor comparison is unnecessary for this fixed-coefficient
presentation. The actual tensors are sheafified scalar extensions, so their Hom
adjunctions provide a shorter construction with the required normalization. The
root section clause can be obtained directly from the fixed Cartier isomorphism and
evaluated kernels. No statement repair, disputed statement, target change, or
forced consumer adaptation was needed.

Preflight required a change record for the proof-local elaboration commands and
private import changes. See
`coord/changes/finite-root-site-comparison-proof-interface.md`. The downstream
source scan reports no current Lean importers; the DAG parent and unit route are
retained. No consumer adaptation is required because all public signatures,
definitions, attributes and public imports are preserved.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
