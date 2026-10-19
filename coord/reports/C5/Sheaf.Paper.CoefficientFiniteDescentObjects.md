## What changed

Completed `AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects`, preserving
its signature, universes, visibility, public imports and documentation. This reuses
F3's previously delivered proof from commit e4ed025f6e0e815413104b4de9e43a31cfbb0db7,
which was subsequently removed by a batch rollback. It is checked again against the
current library in this session; its earlier delivery is not treated as current
verification.

The private proved helpers `free_hasConstantModel` and
`constantModel_eq_of_localFree` identify finite constant local models with the source
library's constructibility predicate for the finite-field and algebraic-closure
coefficients on Noetherian schemes. Finite free modules pull back from the point,
including rank zero. Each stratum has a Noetherian underlying space. The existing
same-unit `constructibleCocone_essSurjObj` then supplies the finite-field model.
`boundedConstructible_derivedExtendScalarsSubfield_obj` and
`derivedExtendScalarsCompIso` establish persistence for every finite enlargement.
No object is defined by choosing a witness of an unproved existence theorem.

Added only the proof imports `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`
(with `all` for its proved private transport/local-triviality helpers) and
`Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`. Updated the node proof,
proof dependencies and proof origin. The change record
`coord/changes/coefficient-finite-descent-objects-proof-commands.md` documents the
proof namespace openings; no consumer adaptation or public signature change is needed.

Validation in this session: direct `lcompile.py` succeeded, as did sandbox-wide
`lcompile.py --all`. Both added proof imports passed import-direction checks.
The first completed dry run timed out at the local compilation gate; the retry
passed that gate and returned only two metadata findings (the restored change
record's landed status and its missing report reference), both now repaired. The
resumed final dry run passed compilation and preflight (commit ec88c609a7), with
review class CODEX for the node update, change record and namespace openings.
Searches through `msearch.py` used LeanFinder, Loogle and grep; none supplied a
Mathlib replacement. The existing source theorem is the shorter route. The argument
covers empty schemes and strata, zero rank and zero complexes, the base field, and
an enlargement with E = F.

## Proved and sorry left

Closed the one original hole
`AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects`
(node `det-lem-coefficient-finite-descent-objects`), proving both conjuncts.
The two new private helpers are fully proved. Holes closed: 1; holes added: 0;
split off: 0. No `sorry` remains in the delivered module. No new module is added.
Existing dependencies retain their own proof status; no claim is made about
eliminating their transitive holes.

## No longer needed

Removed these direct proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.Paper.CoefficientFiniteDescentHom`
- `Sheaf.Paper.CoefficientFiniteDescentLisse`
- `Sheaf.Paper.CoefficientHeartGeneration`
- `Sheaf.Paper.CoefficientHeartTriangulated`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
- `Sheaf.SixFunctors.ScalarSixPullback`

The local proof no longer separately invokes these planned nodes:

- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-sfb-subfield-flat`
- `lem-sfb-qlbar-flat`
- `det-cor-coefficient-heart-ii-triangulated`
- `def-weil-finite-subextension-directed-set`
- `sk-def-sfb-change-of-scalars`
- `sk-def-sfb-derived-categories`
- `det-lem-coefficient-finite-descent-hom`
- `def-weil-triangulated-category`
- `lem-sf-triangle-morphism-iso`
- `det-lem-coefficient-finite-descent-lisse`
- `det-cor-coefficient-heart-ii-generation`
- `det-prop-scalar-six-pullback`

The already implemented same-unit `lem-sfb-constructible-cocone-obj` supplies source
bounded-constructible models. Its proof uses sheaf descent, morphism descent and
bounded triangulated devissage, retaining the unit's route. The removed direct
imports may remain transitive dependencies or be used elsewhere; this is local
pruning, not a claim that all are globally unreachable. Removed the obsolete
top-level `det-prop-scalar-six-pullback` tool-use entry. The four original public
imports remain unchanged. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original five-step direct proof is a valid plan, but source-library object
descent already exists. The remaining comparison concerns finite constant models
versus stratified local finite presentation for the two field coefficient choices
on Noetherian schemes. No implication for arbitrary condensed coefficient rings or
arbitrary non-Noetherian schemes is asserted. No statement is disputed or weakened.
The restored change record's historical landed status was reset to open for this
new delivery, and its report reference was added after preflight requested it.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
