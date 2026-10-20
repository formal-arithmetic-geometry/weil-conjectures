## What changed

Repaired the returned stale-base delivery against the current item source. The current
source uses `WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact` and
`WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf` after retirement of the
corresponding `Sheaf.*` copies. Preserved both current public imports and reapplied
the two complete proofs. Existing signatures, public imports and data definitions
match the current source exactly. No downstream adaptations are required.

Proved both holes of `Sheaf.CategoryTheory.LocalizedModuleExactIndependent` without
changing any existing declaration signature, definition, visibility, or public import.
Added proof-only imports of `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor` and
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.

The private direct-sum Hom construction reuses the proved argument in
`LocalizedModuleExactForSystems`, specialized to the original module's site and coefficient
universes. No new universe command remains in the file.
It composes the explicit direct-sum Hom equivalence with module sheafification.
Its unit has the required insertion formula definitionally; `Adjunction.ext` proves
uniqueness from that formula. No arbitrary witness of a mere existence theorem is used
to construct data. The existing public adjunction remains selected from its uniquely
normalized existence theorem.

For exactness, restriction is additive sectionwise. The adjunction supplies additivity
of extension, colimit preservation of extension, and limit preservation of restriction.
Sectionwise injectivity and `DirectSum.lmap_injective` show extension preserves monos;
left exactness of module sheafification preserves these monos. The abelian exactness
criteria give extension's finite-limit preservation. Abelian slice restriction preserves
colimits by the cocontinuous site adjunction. The exact faithful module forgetful functor
then reflects finite-colimit preservation back to module restriction.

This follows the current four proof steps of
`lem-pur-site-restriction-module-adjunction-exact` (Stacks 03DI and 03DJ), so its existing
proof and dependencies need no change. That node is currently attached to the more
general `LocalizedModuleExactForSystems` module; its route also proves this older
interface. The unit `sk-def-sf-operations` has no realized statement or proof steps
bypassed by this delivery. Empty direct-sum indexing sets and zero module sheaves are
covered by the direct-sum universal property and injectivity argument without any
nonemptiness assumption.

## Proved and sorry left

Closed 2 of 2 original holes:

- `SheafOfModules.localizedModuleExactIndependent`.
- `SheafOfModules.localizedModuleAdjunctionIndependent_existsUnique`.

Both realize `lem-pur-site-restriction-module-adjunction-exact`.
No holes remain in the item. No holes or modules were added or split off.
All private helpers are proved, and all data definitions are explicit constructions.
The reconciled version compiles without warnings through `lcompile.py` in
12.8 seconds. The updated scratch audit compiled in 30.8 seconds and reports
exactly `propext`, `Classical.choice`, and `Quot.sound` for both proved theorems
and `SheafOfModules.localizedModuleDerivedAdjunction`. No `sorry` remains in the
module. Audit commands stay in a scratch copy and are absent from the delivery.

## No longer needed

No imports or modules were removed from the existing public interface. Both added
proof-only imports are used. There are no newly pruned DAG nodes or modules.

The proof does not use the abelian extension comparison route described in the old
exactness docstring: `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`,
`lem-weil-pbc-site-extension-by-zero-exact`, `lem-weil-pbc-site-restriction-adjunction`,
and `lem-weil-pbc-site-restriction-exact` are unnecessary as proof dependencies here.
The current DAG already omits these in favor of the direct monomorphism argument.
Their modules may still occur transitively in the retained public import interface;
this is not a claim to have pruned them from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The current node's `lean` attachment is to `LocalizedModuleExactForSystems`, not this
item module; searching only for this module in the nodes yields no attachment.
The blueprint identifier in the item's docstrings identifies the shared mathematical
node. The item's old exactness docstring describes a longer abelian-extension
comparison route, whereas the current node already records the shorter proof used here.

`LocalizedModuleExactForSystems` already proves the corresponding general interface,
but publicly imports this item, so importing it here would close a cycle (confirmed
by `tools/import_direction.py may`). Reusing its explicit private proof construction
avoids that cycle and changes no other module. The proof depends on no unproved new
statement and requires no repair of definitions or downstream consumers.

The previous repair's dry runs were killed with exit code 137 before diagnostics.
The first dry run of this repair failed in `sharedrepo.worktree` before Lean
validation: its `git checkout -q --detach origin/sheaf-dag` subprocess timed out
after 600 seconds. The retry reached compilation but its full-probe compile
timed out at 60 seconds. A diagnostic scratch copy with the exact project probe
and profiler then compiled in 16.6 seconds (`SHEAF-PROBED 12`, no forbidden axioms).
The largest reported proof step was 2.18 seconds and the probe elaboration was
5.67 seconds; no expensive definition was identified. Diagnostic options and
probe commands are absent from the delivered file. The following required dry
run passed compilation and preflight: `OK (dry run)`, commit `9babc81805`, review
class `CODEX: repair of a returned delivery`.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
