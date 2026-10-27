## What changed

Implemented `AlgebraicGeometry.ProEtale.CondensedRing.qcqs_proper_open_boundary_vanishing`
without changing its signature. The proof computes the inverse image of the closed boundary,
applies closed base change to the open extension of a finite-Tor constructible generator,
uses mixed open/closed vanishing, and extends vanishing through a replete triangulated
localizing kernel. Properness and quasi-compactness supply the geometric instances.

Added `Sheaf.CategoryTheory.Triangulated.LocalizingSubcategoryUniverse` with the proved
`CategoryTheory.isLocalizingSubcategory_of_locallySmall`. Its explicit nonzero-support
argument reconciles the hom-universe-indexed coproduct interface of the boundary-functor
lemma with the object-universe-indexed public definition `localizingClosureProEtale`.
Its private support lemma proves the idempotent-endomorphism injection directly, following
the existing source proof; no source-library declaration was changed.

Added `Sheaf.Paper.QcqsFiniteValuedAlgClClosedBaseChange` for the seventh admissible
coefficient case. This is proper closed base change on arbitrary bounded constructible
finite-Tor inputs; it assumes neither open support nor membership in a localizing hull.
The original closed-base-change declaration remains unchanged and supplies the first
six coefficient cases. Proof imports are private. Updated the item's DAG route and
provided nodes for both new statements.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.qcqs_proper_open_boundary_vanishing`
(node `lem-sfb-qcqs-proper-open-boundary-vanishing`). Its module has zero holes.

Added one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.qcqs_finiteValuedAlgCl_closed_baseChange`
(node `lem-sfb-qcqs-finite-valued-algcl-closed-base-change`). This is a decomposition:
one original hole closed, one strictly separate coefficient-case obligation added,
net zero holes. No claim of an unconditional new proof is made. Every other declaration
in the packet is proved, including the categorical universe lemma and private helpers.
The retained theorem has its source and a complete coefficient-generation proof in words.

## No longer needed

Removed these original private proof imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
- `Sheaf.CategoryTheory.ModuleObjects.LiftExact`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.Topology.Constructible`
- `Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula`
- `Sheaf.SixFunctors.OpenTensorNormalizationData`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Sheaf.AlgebraicGeometry.QcqsProperLocalizingCoproducts`

Their roles are already provided by the declared open-extension and boundary-functor
lemmas. In particular this proof does not reconstruct scalar-model stratifications,
prove projection formulas, or rederive the functors' coproduct comparisons. These imports
can remain transitive dependencies of their owners; no whole-library withdrawal is claimed.

Removed stale item-level tool-use entries `lem-sfb-alpha-iso`,
`det-pe-topos-functoriality-inverse-image`, `det-prop-sfb-module-pullback-exact-lifted`,
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-weil-pbc-exact-functor-complex-cohomology`,
`lem-sfb-condensed-support-projection-formula`, and
`lem-weil-pbc-left-adjoint-preserves-colimits`: their mathematical operations are delegated
to the two existing extracted lemmas. All existing direct proof-dependency nodes remain
needed. No existing module or declaration is withdrawn; no source-library file is changed.

## Where the brief, the DAG or earlier work was wrong

The planned application of `qcqs_proper_constructible_closed_baseChange` does not typecheck
for the full item: its hypothesis is the six-case
`IsNormTopologicalLocalizingAdmissibleCoefficient`, whereas this item's
`IsLocalizingAdmissibleCoefficient` has a seventh, finite-subextension-valued
`Profinite.padicAlgClRingObj` case. The continuous-map coefficient and the finite-valued
coefficient are distinct and are not identified here. The existing base-change module is
held by N1; its interface was preserved. The missing case is explicitly isolated instead
of silently strengthening N1's theorem or dropping the seventh disjunct.

Also, the public localizing closure uses object-universe coproduct indices while the
boundary-functor interface uses the hom universe. Repleteness alone does not identify
the two closures. The proved new indexing-universe lemma supplies the required argument.

The new coefficient-case theorem is checked on zero complexes, empty schemes, c=id,
and f=id; each reduces to the usual invertible exchange. Its proposed proof uses finite
extensions of shifts of integral generators and does not descend arbitrary morphisms or
entire complexes to one finite field. The generic universe lemma includes entirely zero
families and empty support and makes no assertion that larger coproducts exist.

## New nodes

`lem-sfb-localizing-subcategory-universe` realizes the proved generic indexing-universe
argument used by the kernel assembly. It belongs below the refinement unit. Its proof
constructs the coordinate idempotents and the restricted colimit explicitly; no step
of the purity unit is substituted for a refinement step.

`lem-sfb-qcqs-finite-valued-algcl-closed-base-change` records the missing coefficient case
of the closed-complement calculation. Its four-step proof is coefficient-isomorphism
transport, integral generation, normalized scalar exchange using the bounded-below
algebraic-closure direct-image comparison, and finite triangulated devissage. This is a
separate exchange result without the item's support or localizing hypotheses. All cited
obligations already have Lean declarations. No change record is required: no existing
statement or definition changed.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
