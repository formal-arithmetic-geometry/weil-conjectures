## What changed

Proved `AlgebraicGeometry.Etale.isIso_kunnethGlobalSectionsMap_of_isProper` in
`Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections`, without changing its signature,
visibility, public imports, or any definition. Clause (b) of the existing compatibility
theorem already includes `IsIso` of the specified general-base `kunnethMap`. Extract
that assertion and unfold `kunnethGlobalSectionsMap`: tensoring the inverse Leray
comparisons, the point tensor comparison, the functorial image of `kunnethMap`, and the
final Leray comparison are all isomorphisms. The proof uses only
`Sheaf.AlgebraicGeometry.KunnethMapAgrees` as a direct proof import.

The node `lem-kun-0f14b` now records these two steps and their actual direct dependencies.
The unit route is preserved: the same proper-base-change/projection-formula argument is
packaged in the cited compatibility theorem, not replaced by the general finite-type
Künneth theorem. Read the current unit and compatibility source, and checked the canonical
map's explicit definition and the `sq.w.symm` orientation. The argument handles n = 1,
empty factors and arbitrary unbounded inputs without new restrictions.

Searches run through msearch.py: LeanFinder for the proper/finite-type separably closed
Künneth assertion returned eight scheme-pullback facts and no matching theorem; Loogle
for `"IsIso", "map"` returned `CategoryTheory.Functor.map_isIso` and related transport
facts; grep for `kunnethGlobalSectionsMap|kunnethMap_agrees` returned no Mathlib hits.
Local rg found the exact compatibility declaration and the upstream general finite-type
Künneth theorem. The compatibility declaration is the direct dependency with the exact
hypotheses needed here.

Validation: the item compiled through lcompile.py; delivery preflight additionally
compiles the declaration with its axiom and direct-sorry probes.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_kunnethGlobalSectionsMap_of_isProper`
(blueprint `lem-kun-0f14b`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered Lean module. The existing imported
`kunnethMap_agrees_with_leray_projection_formula_modN` remains an existing dependency;
its proof is not modified or counted as newly proved by this delivery.

## No longer needed

Removed these direct proof imports:

- `Sheaf.EtaleCohomology.KunnethOneProper`
- `Sheaf.AlgebraicGeometry.ProperStability`
- `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`
- `Mathlib.GroupTheory.Torsion`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN`
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedPointCohomologicalDimension`
- `Mathlib.FieldTheory.IsSepClosed`
- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.EtaleCohomology.SepClosedFieldVanishing`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`

No longer separate direct proof dependencies of `lem-kun-0f14b`:

- `lem-kun-proper-stability`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-kun-0ezp`
- `def-kun-constant-sheaf`
- `def-kun-rgamma-unbounded`
- `def-kun-derived-tensor`
- `lem-kun-0f0c`
- `lem-kun-pullback-constant`
- `lem-kun-0f0g`
- `def-weil-size-convention`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-kun-0f10`
- `lem-kun-0f12`
- `lem-kun-tensor-sym`

Their required mathematics is supplied through the existing compatibility theorem
and the canonical comparison definitions. This is direct-import pruning; modules still
reachable through those dependencies are not claimed to be globally unreachable.
Also removed the obsolete direct `tool_uses` approval for
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`: the proof no longer applies
that theorem directly. Retained both public imports because they belong to the existing
statement interface.

## Where the brief, the DAG or earlier work was wrong

The seven-step plan needlessly repeated consequences already included in the stated
conclusion of `kunnethMap_agrees_with_leray_projection_formula_modN`. Its final
`KunnethLerayAgreement` field supplies the required `IsIso` before canonical transport.
No mathematical statement or definition needed correction; no consumer adaptation or
new node is needed.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
