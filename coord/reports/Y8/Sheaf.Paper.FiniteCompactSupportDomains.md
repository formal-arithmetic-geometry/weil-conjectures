## What changed

Proved both declarations in `lean/Sheaf/Paper/FiniteCompactSupportDomains.lean`,
with every existing public signature and public import unchanged. The item source
and its quarantine archive were both present and identical when work began; the
archive and Lean attachment are preserved.

The main proof uses the existing ordinary etale specialization
`Etale.rightDerivedLowerShriekOfCompactification_isTriangulated_and_ctf` for the
exact supplied compactification, and `finiteCoefficientInputModels` for actual
scalar extension, intrinsic site pullbacks and their Tor intervals. Private,
proved helpers translate the two existing constructibility/Tor APIs, assemble
the domain clauses, and preserve lower bounds through proetale compact support.
The specified comparison is a composite of the proved qcqs counit mate and the
right-derived image of the canonical open-comparison isomorphism.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
The unit's compatibility statement and steps remain intact: this only simplifies
finite-domain verification below its coefficient-compatibility step. No new
public declaration, source-library edit, definition repair or consumer adaptation.

Searches: LeanFinder for compact-support preservation gave unrelated affine
transition and generic derived-bound lemmas; Loogle confirmed functorial
preservation of isomorphisms; Mathlib grep for compactification preservation had
no match. Library `rg` found the direct ordinary etale compactification theorem
and the already-proved finite-input models, and their signatures and proofs were
read before use. The field-characteristic exponent calculation supplies the
precise invertibility hypothesis of the ordinary etale theorem. No assumption of
flatness or finite projective dimension of B over A is introduced.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.ProEtale.finiteCompactSupportDomains`
- `AlgebraicGeometry.ProEtale.finiteCompactSupportDomains_comparison_isIso`

Added 0 holes; split off 0 statements. No `sorry` remains in the item or its private
helpers. Both theorem signatures are byte-for-byte unchanged. The Tor witness is
widened to `[min a b,b]` when an upstream existential does not include ordering;
this also handles zero complexes without assuming the original witnesses ordered.
The zero coefficient ring, empty schemes and zero inputs are retained.

## No longer needed

Removed these private proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`
- `Sheaf.Paper.CompactificationLocalizing`
- `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The elementary geometry and exact-derived APIs are available through the retained
statement imports and the new proof imports. The former internal-module route is
unnecessary: the item no longer uses `det-pe-finite-tor-comparison-noetherian`,
`lem-sf-module-object-ordinary-coefficient-equivalence`, or
`lem-sp-unbounded-finite-tor-comparison-reflection`. It uses the existing ordinary
etale specialization of `det-sf-comp-coherence-single` instead of the
`CompactificationLocalizing` declaration. It uses the direct qcqs mate proof
instead of the larger `lem-sp-finite-compact-site-coherence` package. It obtains
scalar preservation from `lem-sp-finite-coefficient-input-models`, so there is no
direct proof edge to `det-sp-scalar-extension-functor` or
`def-weil-pbc-witness-compatibility` here. Their existing public imports stay
unchanged; no claim is made that these modules are globally unused or withdrawn.
Obsolete top-level tool-use entries were deleted in original order.

## Where the brief, the DAG or earlier work was wrong

The former plan took a longer route through internal condensed-module
compactification preservation, ordinary-module equivalences and unbounded
reflection. The source library now already proves the exact ordinary etale
compactification preservation needed, and finiteCoefficientInputModels proves the
other domain clauses directly. The original declaration docstrings are preserved
as the historical plan; the updated DAG records the actual proof.

No false statement, target change or tool workaround was used. All edits are in
the assigned sandbox, and compilation/delivery use the launcher tools.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
