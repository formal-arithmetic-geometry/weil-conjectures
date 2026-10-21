## What changed

Proved `SheafOfModules.finite_ring_action_local_constancy` in
`Sheaf.CategoryTheory.FiniteRingActionLocalConstancy`, without changing its signature,
public imports, coefficient universes, or constant-module definition.

The proof restricts scalars along the existing constant commutative ring unit. The
resulting fixed-ring module sheaf has the same underlying set sheaf. The private
`finite_constant_refinement` follows the proved finite-operation construction in
`WeilConjectures.CategoryTheory.Sites.ConstantForget`, reusing its label-section
identities and retaining the actual finite image submodule that its public theorem
forgets. Its sheafified map is locally bijective. Private proved comparison maps
identify ordinary constant module sheaves with the recorded module realization,
commute constants with localization and relocalization, and lift the resulting
isomorphisms through fully faithful scalar restriction. Finally, induction on the
generated topology gives actual covering presieves, which are composed using bind.
All helpers are private and proved; no source-library module is changed.

Change record:
`coord/changes/finite-ring-action-local-constancy-private-scope.md` records the
added proof-local section variables, namespace opens and elaboration option, as
required by server preflight. The downstream query reports zero current importers
and only the item itself mentions the public theorem; no adaptation is needed.

Added proof imports of `WeilConjectures.CategoryTheory.Sites.ConstantForget`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, and
`Mathlib.Algebra.Category.ModuleCat.FilteredColimits`. Updated the existing node's
proof, proof dependencies and proof origin to record this route, and removed its
obsolete tool-use entry.

Validation: the complete module compiled cleanly through `lcompile.py`; the final
cleaned module compiled in 40.6 s.
`#print axioms SheafOfModules.finite_ring_action_local_constancy` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. The diagnostic command was then
removed. The construction covers empty label sets, empty covering families,
empty-covered objects and the zero ring: it makes no injectivity assumption on the
label map, and zero is included among the finite operation tests.

## Proved and sorry left

Closed one of one original holes:
`SheafOfModules.finite_ring_action_local_constancy`
(blueprint: `lem-sp-finite-ring-action-local-constancy`).
Added zero holes; split off zero statements. No sorry remains in the delivered
module, including its private helpers. This is a proof, not a decomposition.

## No longer needed

Removed the proof import
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` and the proof
dependency/tool-use `lem-weil-pbc-site-sheafification-sections-local`.
Mathlib's `imageSieve_mem` and `equalizerSieve_mem` applied directly to the genuine
sheafification units supply exactly the local representation and equality used in
the argument, without that theorem's stronger precoverage composition assumptions.

Removed the unused plain import
`Mathlib.CategoryTheory.Sites.PreservesSheafification` and the dependency
`lem-pc-sites-sheafification-underlying-sets`. The proof instead checks the local
bijection of the linear unit directly against its underlying additive
sheafification unit, and uses the ModuleCat local-bijection criterion. No separate
set-sheafification comparison is needed.

All other planned dependencies are retained, together with the existing
constant-module constructor's owning node. No entire library module is withdrawn;
other consumers may still need either removed dependency. The unit route stays
unchanged, and no target statement or definition is changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The planned arbitrary-site local
representation theorem was unnecessary and has stronger covering-composition
hypotheses than `IsSiteForCoverings`; using the generic Mathlib sheafification-unit
APIs avoids this mismatch. The adopted ConstantForget theorem concludes only
`IsConstant`, so applying it verbatim would discard the finite model required here;
its existing construction supplies the stronger finite witness when retained.

Searches through `msearch.py` (LeanFinder, Loogle and grep) and local `rg` found no
ready theorem with the required finite ringed-module conclusion. Read Stacks
`sites-modules.tex`, Tag 093S (proof omitted), `sites.tex`, Tag 00WK, the item and its
stated dependency records, and the full adopted ConstantForget proof. The actual
finite-operation proof remains the DAG's route, with fully proved interface glue.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
