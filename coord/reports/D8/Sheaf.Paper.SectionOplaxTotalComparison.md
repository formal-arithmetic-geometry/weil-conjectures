## What changed

Proved `AlgebraicGeometry.ProEtale.ModuleRingedComparison.section_oplax_total_comparison`
from the existing ordinary normalization and signed-cochain tensor APIs. The proof computes
both total comparisons on every bidegree injection. A private categorical pasting lemma
assembles the ordinary square, and preserved-coproduct extensionality gives the total
square. Cancellation gives the inverse equations; evaluation gives the scalar formulas.
The unit calculation uses ordinary normalization in degree zero and a zero source in
other degrees. The existing cochain oplax structure supplies naturality, associativity,
and both unitors. Functoriality gives the homotopy and derived image equalities.

The theorem signature and `TotalMapAgreement` remain unchanged. In the scalar clauses
of `SectionTotalNormalization`, two inferred ordinary module arguments are made explicit.
The complete proposition remains definitionally equal to its original formulation.

Adapted three unclaimed modules to keep these comparisons usable within the compile limit.
`SectionTotalOplaxComparisonData` retains the canonical tensor structures through explicit
reducible aliases and eight proved property caches, explicitly types the three existing
termwise functors and the existing total tensor comparison, and exposes the proved equality
of the actual internal oplax structure with the canonical composite. The section tensor
isomorphism stores its original forward and inverse maps explicitly. The five-factor
conjugation similarly stores both maps, with proved inverse laws and equality to the
original composition. `SectionOrdinaryOplaxNormalization` gives five existing reducible
map aliases explicit morphism types, retaining their bodies and all existing proofs.
`InternalAbelianSheafModuleEquivalence` retains the original construction as
`sectionModuleEquivalenceCore` and stores the same equivalence with its forward functor
explicitly recorded. The complete equivalence is definitionally unchanged.

All changes are under `Sheaf`. Existing `WeilConjectures` declarations, attributes,
imports, and constructions are untouched. The existing nodes describe the direct proof
and attach the added implementation helpers; no new node is introduced.

Change records:

- `coord/changes/D8-section-oplax-total-proof.md`
- `coord/changes/D8-ordinary-normalization-map-types.md`
- `coord/changes/D8-section-equivalence-projection.md`
- `coord/changes/D8-total-normalization-module-arguments.md`

Each record lists the current downstream consumers and claim holders. Definition-dependent
targets are reopened for the independent statement review.

## Proved and sorry left

Closed the item's single original hole:
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.section_oplax_total_comparison`
(node `lem-pd-section-oplax-total-comparison`). Closed: 1. Added: 0. Split off: 0.
There is no remaining `sorry` in the item or any other delivered Lean file. The other
three adapted modules had zero holes and retain zero holes.

The four actual candidate files compiled without warnings: equivalence 28.5 seconds,
ordinary normalization 61.0 seconds, total data 28.4 seconds, and item 59.1 seconds
(the compilation tool accepted each file within its enforced limit; these are its
reported wall times). The complete direct proof in the isolated benchmark was audited:
`#print axioms section_oplax_total_comparison` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`.

All 21 final preservation checks passed. The equivalence's complete equality to its
original record and its forward-functor equation are `rfl` (2.0 seconds). All five ordinary
maps equal their original constructors by `rfl` (4.0 seconds). Thirteen data checks cover
the original canonical structures, all retained tensor and unit constructors, the full
conjugation, the typed tensor comparison, and all three termwise functors (33.1 seconds).
The complete proposition equals the original verbatim proposition by `rfl` (40.8 seconds).
The final-file axiom audit in that last probe reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The equivalence, ordinary normalization, and exported
internal-oplax equality likewise use only these axioms.

All five original direct consumers compiled against the final data and proof:
`InternalOplaxResolvingComponents`, `SectionDerivedRepresentativeSquare`,
`SectionResolutionConjugationIdentities`, `SectionResolvingOplaxConstraintData`, and
`SectionDerivedTensorNormalization`. The compiler accepted the batch without errors;
`InternalOplaxResolvingComponents` retains its existing unused-section-variable warning.
Reported consumer wall times were 29.0, 36.1, 29.0, 15.5, and 83.5 seconds respectively.
No consumer source or signature is adapted. Delivery preflight is pending.

## No longer needed

The proof does not use the planned nodes `lem-pd-total-oplax-conjugation-summands`,
`lem-pd-total-oplax-conjugation-constraints`, or
`lem-pur-cochain-pullback-tensor-coherence`. The existing proved single-functor summand
and cochain-monoidal APIs (`lem-sfb-termwise-strong-monoidal`), ordinary normalization,
and coproduct extensionality suffice. These three proof edges and the obsolete
cochain-coherence `tool_uses` approval are removed from the item's node. The existing
internal/section tensor-comparison approval is retained.

Removed direct imports:

- The public `Sheaf.Paper.SectionOrdinaryOplaxNormalization` import is redundant through
  the data module. A private `import all` accesses its proved component lemmas efficiently.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`: its specialized result is unused.
- `Sheaf.Topology.ProfiniteCondensedRing`: reexported through the data module.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: no flatness hypothesis is used.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: the generic localization
  API suffices when mapping equal chain maps.
- `WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex`: reexported through
  the data module and used through that import.
- `Mathlib.CategoryTheory.Adjunction.Limits`: already reexported through the module APIs.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`: reexported through the data
  module; its specified ordinary comparison remains part of the retained construction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`: no derived tensor
  construction is needed for the image of a chain-map equality.

`Mathlib.Algebra.Homology.DerivedCategory.Basic` is imported publicly for the statement's
localization API. No module is withdrawn, and no upstream declaration or proof is removed.
Other parents' uses of these modules remain valid; this delivery prunes only its own
unused import and proof-dependency edges.

## Where the brief, the DAG or earlier work was wrong

The planned generic conjugation lemmas are unnecessary for this item. Their needed
summand calculations follow directly from the already proved single-functor API and the
ordinary transport square. The actual internal total tensor uses the specified mate,
whereas the local generator maps use the canonical composite structure. The existing
proved `internalPullOplax_eq_canonical` identifies those structures; a definitional
identification is not assumed. The mathematical statement, arbitrary integer-indexed
complexes, infinite degreewise sums, and the unit's route are preserved.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
