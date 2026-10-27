## What changed

Filled `AlgebraicGeometry.ProEtale.SemilinearProperOpen.DiagramShift.diagramOpenClopenShiftModels`
without changing its statement or the public model structures. The proof constructs the ordinary
open compositor and restriction from adjunctions and verifies their localization by the existing
mate-comparison theorem. Complementary restrictions give product equivalences with explicit
biproduct inverses, for systems, complexes and derived categories. The ordinary comparison and
projection are identified with the prescribed derived maps by normalized unit equations.
All helpers are private and proved. The shift compositor calculation is proved generically
for adjunctions before applying it to systems, avoiding repeated expansion of the sites. The node's proof and dependencies follow this argument.

The specified direct-image shift uses `canonicalRightDerivedAdjunctionShift`; the open shifts use
`mapExactDerivedCategory_unit_commShift`. No resolution is selected in this module. The identity compositor laws follow directly from
section-normalized direct-image identity maps, adjunction mates and localization, using the
generic pullback-site and descent lemmas of `StrictTowerDirectImageCoherence`.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.SemilinearProperOpen.DiagramShift.diagramOpenClopenShiftModels`
(node `lem-pur-diagram-open-clopen-shift-models`), the module's original one hole.
Added: zero holes. Remaining in the delivered module: zero. No statements were split off.
Existing imported declarations with unfinished proofs remain dependencies under the stage-3 rules.

## No longer needed

Removed private imports:

- `Mathlib.CategoryTheory.Localization.Predicate` (available through the actual localization API);
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`;
- `Sheaf.Paper.SequenceSiteOpenExtension`;
- `Sheaf.CategoryTheory.ExactDerivedAdjunction` (already exposed by the statement imports);
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`;
- `Sheaf.Paper.DerivedAdjunctionShift`;
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`;
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence` (the direct identity proof avoids
  transporting the complete varying-ring coherence theorem between chosen-adjoint APIs).

The new argument does not directly use the planned nodes
`lem-pur-sequence-site-open-extension`, `lem-sfb-exact-derived-natural-iso`,
`lem-weil-pbc-kinjective-shift`, `lem-weil-pbc-derived-adjunction-shift`,
`prop-pur-kinjective-resolutions-exist` or `lem-pc-kflat-resolution`. It also does not use
`lem-sf-semilinear-compositor-coherence`: the required identity clauses are proved from
section formulas and generic categorical identities.
The canonical shift theorem supplies the prescribed right-derived normalization, and the actual
ordinary extension API supplies the disjoint vanishing. The existing exact functor localization
API supplies termwise natural transformations. Removed the corresponding obsolete `tool_uses`
entries for sequence-site extension, the general geometric derived-adjunction shift,
K-injective existence and K-flat resolution. Retained the clopen gluing and exact-derived
comparison approvals. No module is withdrawn: these nodes may still be needed by other consumers
or by the adopted source library.

## Where the brief, the DAG or earlier work was wrong

No statement was weakened or disputed. The former resolution-level proof plan was unnecessarily
long for the available canonical shift API. The explicit biproduct inverse also avoids choosing
an undetermined system-gluing witness. The original unit route is preserved; its realized list
imposes no additional steps on this node.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
