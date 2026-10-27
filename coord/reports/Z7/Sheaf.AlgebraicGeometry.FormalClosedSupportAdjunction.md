## What changed

Repair of returned head `9e39d280ab7` (reviewer `C-9e39d`). The mathematical review
passed. Landing failed because an `--apply-fixes` entry named only
`Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction.md`, which is not a delivery path.
The report in this packet is delivered at its canonical repository path:
`coord/reports/Z7/Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction.md`.
Any report fix must use that full path. The sandbox input remains `report.md`, as required
by `deliver3.py`; no extra report or unrelated file is introduced. The reviewed Lean proof
is retained and checked again against the current published build. Delivery constructs
the new commit on freshly fetched `sheaf-dag`.

Proved `AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_adjunction`
with its exact original signature. Consolidated the duplicate pullback adjunction as an
abbreviation of the completed `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`
API, now publicly imported. The change record is
`coord/changes/Z7-formal-support-aliases.md`; it inventories all downstream consumers.
All other original definitions and instance proofs are retained verbatim.

Reused the completed sheaf adjunction, normalized counit, injective-unit epimorphism and
global Hom-complex isomorphism. Private proved helpers generalize its recollement argument
to the arbitrary derived-model universe `w` of this theorem. Comparing rotated triangles
and applying closed inverse image proves the fibre clause for every distinguished fibre.
No cone choice or new unproved mathematical input is introduced. The item node records
this proof route. Existing declaration types and docstrings are retained.

The new private proof imports are `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact`,
`WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`,
`WeilConjectures.CategoryTheory.Triangulated.Recollement`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful`.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_adjunction`
(node `lem-route-formal-closed-support-adjunction`): 1 of 1. Zero holes added or split off.
Every new private helper is proved. No textual `sorry` remains in the item's Lean file.
The proof uses existing project theorems, as intended by stage 3.

## No longer needed

Removed these original private imports:

- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`

The completed support API supplies the sheaf constructions directly. Thus the original
`lem-sfb-noncommutative-ringed-open-closed` and
`lem-sfb-sheaf-modobj-grothendieck-any-ring` are no longer direct proof dependencies.
There is no assertion that they are globally unused or may be withdrawn.

Also removed from this node's direct proof dependencies:
`def-sp-injective-resolutions`, `lem-pur-kinjective-degreewise-existence`,
`lem-sfb-alpha-iso`, `lem-weil-pbc-complex-ses-triangle`,
`lem-weil-pbc-kinjective-hom-derived`, `lem-weil-pbc-right-adjoint-preserves-limits`,
and `lem-weil-pbc-termwise-adjunction-homotopy`. The corresponding seven obsolete
top-level `tool_uses` approvals are removed without adding or reordering approvals.
Injective objects and the coefficient isomorphism remain statement dependencies and
are used in the existing constructions; they are not separate steps of this new proof.
The generic recollement theorem replaces the resolution-and-short-exact-sequence route.
No module is withdrawn; the unit's support-kernel route is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned new noncommutative localization route duplicated a completed module.
`CondensedClosedSupportAdjunction` already proves the required sheaf assertions and Hom
formula. Its derived theorem fixes the Grothendieck derived-model universe, whereas
this item's universe `w` is arbitrary; its recollement proof works at `w` without an
additional hypothesis. The old duplicate scalar-transport presentation was difficult
to transport through dependent kernel types, so the adjunction is consolidated under
the project's duplicate-definition rule. This changes presentation, not the prescribed
support functor, adjunction maps, or theorem meanings; the required definition review
is explicitly recorded in the change record.

The fibre clause here quantifies over every distinguished fibre triangle. Comparing
rotated triangles is more direct than computing a mapping cone. No statement dispute
or new DAG node is needed.

A remote scratch validation proved equality of the old and consolidated scalar and
module adjunctions, and hence equality of their kernel functors. The validation has no
holes and compiled successfully (20.9 s); it is not an additional library declaration.
The original kernel definition is retained. No downstream source is changed.

Validation of the returned head: the item alone compiled cleanly in 43.4 s. An ordered
compile rebuilt the item in 44.1 s and its immediate importer
`FormalClosedPullbackProducts` in 13.0 s; `FormalClosedSupport` then reached the 60-second
limit, so the batch stopped before `FormalClosedSupportII`. No downstream file is changed.
The broader transitive-consumer check encountered elaboration timeouts; those
are not reported as successful checks. Delivery runs the project axiom probe and preflight.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
