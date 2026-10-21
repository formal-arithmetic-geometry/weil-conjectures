## What changed

Filled the eight remaining proof holes in
`lean/Sheaf/Paper/FiniteStagePairCategory.lean`. All existing public signatures,
definition bodies, public imports, and blueprint statements are preserved.

The proof identifies the completed coefficient map with the existing scalar-change map,
reuses the actual integral/rational scalar functors, and proves uniqueness by clearing
localized denominators. The ordinary identity tensor comparison is constructed from
adjoint uniqueness and checked on pure tensors. Its derived comparison follows from the
universal left-derived counit. Associativity and unit equations follow from exact
restriction coherence and adjunction mates, then descend through full integral inclusions
and raw rational localization. Equal fields, including repeated fields in the pentagon,
are included in the proof.

Added only proved private helpers and private proof imports:
`Sheaf.Paper.PbcScalarExtension`,
`Sheaf.Paper.CompletedAdicCoefficientDatum`,
`Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`,
`Mathlib.RingTheory.Localization.BaseChange`,
`Mathlib.Algebra.Module.Torsion.Field`,
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory`,
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`,
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`. The `import all` imports reuse proved
private tensor, resolution, and exact-derived coherence helpers. Local irreducibility
attributes keep chosen comparison definitions from being unfolded during implicit
matching. A local priority for the existing division-semiring torsion-free instance
avoids repeated searches through flatness, finite presentation, and reflexivity when
elaborating the coefficient field. The node copy records the implemented route and its dependencies.
The elaboration-command record is
`coord/changes/pbc-finite-stage-pair-category-proof-elaboration.md`; its consumer table
records that no source adaptation is needed.

## Proved and sorry left

Closed all eight original holes, in namespace `AlgebraicGeometry.Scheme`:

- `pbcAmbientScalarExtension_preserves`
- `pbcRationalScalarExtension_exists`
- `pbcOrdinaryScalarUnit_exists`
- `pbcAmbientScalarUnit_exists`
- `pbcScalarAssociator_exists`
- `pbcScalarAssociator_cocycle`
- `pbcScalarSystem_units`
- `pbcScalarExtension_additive`

Each belongs to `def-weil-pbc-finite-stage-pair-category`. No `sorry` remains in the
module. Added zero holes and split off zero statements. The full module is checked through `lcompile.py` and the delivery compile/probe.
No diagnostic profiler or heartbeat setting is retained. The proof uses already stated
library dependencies; it does not claim those dependencies' remaining proofs are closed.

## No longer needed

Removed the exploratory proof import `Sheaf.Paper.CondensedFlatCoefficientCalculus`
and its node `lem-weil-pbc-condensed-flat-coefficient-calculus` from this proof route.
Only two generic exact-derived unit calculations were needed; they are now proved
privately from the public derived-category identity, composition and whiskering API.
The removal excludes 88 modules from this item's source dependency closure. This does
not assert that the condensed coefficient node is unused by other parts of the library.

No original import, node, module, declaration, or unit step is withdrawn. The
original node had no numbered proof plan; the retained coefficient-change, derived
adjunction, and common-stage quotient route is now made explicit. No auxiliary public
statement or new proof obligation is introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The original node is a definition node with
empty proof fields, although its Lean realization contains the scalar-extension
coherence theorems needed to construct that definition. The node copy records the
actual proof route for those theorems. No definition repair or consumer adaptation is
needed.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
