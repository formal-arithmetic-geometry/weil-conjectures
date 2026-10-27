## What changed

Proved six of the eight original theorems in
`Sheaf.AlgebraicGeometry.ProperOpenClopenProjector`.
The geometry uses `squareLift_clopen` and the complementary open subscheme.
The section decomposition specializes the existing disjoint-cover sheaf bijection
to a two-element family. The ordinary open unit and canonical extension/direct-image
comparison are proved using the fixed-coefficient equivalences and normalized mates.
The section projector is identified with restriction on sections, its open-unit
and zero-complement equations are proved, and these equations are transported
termwise to strict towers and cochain complexes.

All original public signatures, public imports, and definition bodies are unchanged.
Only proved private categorical helpers and private proof imports are added.

Return repair (2026-10-24): removed both duplicate private declarations
`clopen_disjoint_direct` and `clopen_disjoint_extension`. The complementary-component
proof now directly applies the existing source theorem
`AlgebraicGeometry.ProEtale.isZero_upperStar_openImmersionLowerShriek`, transported
through `fixedPull`, `fixedOpen`, and the faithful constant-coefficient equivalence.
The duplicate theorems in `StrictTowerProperOpenCalculus` cannot be imported here:
that module imports this item, so that import would create a cycle. No changes to
that module are needed.
Updated the completed portion of the DAG proof; retained the original route and
dependencies for the two unfinished theorems. No other library module is delivered.

## Proved and sorry left

Closed six original holes:

- `AlgebraicGeometry.ProEtale.StrictTower.properOpen_clopen_geometry`
- `AlgebraicGeometry.ProEtale.StrictTower.clopen_section_decomposition`
- `AlgebraicGeometry.ProEtale.StrictTower.clopenModule_openUnit_isIso`
- `AlgebraicGeometry.ProEtale.StrictTower.clopenModuleToDirect_isIso`
- `AlgebraicGeometry.ProEtale.StrictTower.clopenModule_section_projector`
- `AlgebraicGeometry.ProEtale.StrictTower.clopenTower_section_projector`

Two original holes remain, each with proof exactly `by sorry` and its original
source and proof docstring, both attached to
`lem-cbc-proper-open-clopen-projector`:

- `AlgebraicGeometry.ProEtale.StrictTower.clopenDerived_section_projector`
- `AlgebraicGeometry.ProEtale.StrictTower.properOpen_clopen_projector`

Holes added: zero. Split-off statements: zero. All retained private helpers are
proved. No sorry occurs in a definition. The ordinary arguments allow empty pieces
and arbitrary commutative coefficient rings.

## No longer needed

Removed these private imports, unused by the six completed proofs:

- `Sheaf.AlgebraicGeometry.StrictTowerAdjunctionRealization`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.Algebra.Homology.CochainDerivedAdjunction`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison` (removed in this repair)

The three original public imports remain verbatim. Proofs use the existing concrete
ringed-module gluing and open-comparison APIs, imported privately where appropriate.
The two duplicate private helpers from the returned packet are removed; their
proofs and the adjunction-based disjoint-direct-image detour are no longer needed.
No existing public declarations or modules are withdrawn. Dependencies of the unfinished derived
and final-comparison steps remain in the DAG; removing their unused Lean imports
does not claim those mathematical steps are unnecessary.

The completed geometric proof needs no separate proof edges to
`lem-weil-pbc-open-immersion-base-change`, `lem-weil-pbc-proper-base-change`, or
`lemma-nagata-proper-to-separated-target`: the already proved `squareLift_clopen`
provides exactly the clopen lift. The ordinary normalization proof similarly uses
the concrete equivalences and mate identities rather than the planned abstract
localized-site reconstruction. These changes prune only this item's completed
proof route, not any upstream declaration.

## Where the brief, the DAG or earlier work was wrong

The concrete module gluing and adjunction APIs already supply the ordinary
constructions, so rebuilding them from site axioms is unnecessary.

The derived and Cartesian proofs were written and elaborated in several forms,
but their concrete specializations repeatedly exceeded kernel conversion limits.
The exact-derived cochain unit formula has a complete generic argument, while
specializing it to the specified tower adjunction caused expensive conversions of
localized Hom types. A direct inverse-beta factorization also elaborated, but
assembling it with the concrete alpha component formula caused the same issue.
Generic sharing, explicit universes/instances, stricter elaborator transparency,
and definition-factorization experiments did not yield a checked complete packet.
Those experiments and their dependency repairs are excluded from delivery; the two
original holes are retained honestly. No evaluation-faithfulness assertion is used.

Validation of the return repair: the module compiled in 19.8 seconds; the one
redundant `change` tactic reported by the linter was then removed.

No public statement or definition was repaired. No forced adaptations, change
records, or new DAG nodes are included.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
