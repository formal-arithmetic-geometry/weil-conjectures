## What changed

Proved `AlgebraicGeometry.sheaf_module_isIso_iff_isIso_over_open_cover` with its
statement unchanged. The forward implication uses functorial restriction. The
reverse implication specializes Mathlib's `Sheaf.isIso_of_coversTop` to underlying
abelian sheaves, then reflects isomorphisms through `SheafOfModules.toSheaf`.
Restriction of underlying sheaves agrees definitionally with module restriction.
Replaced the proof import `Sheaf.Topology.GlueSheavesOfModules` with
`Mathlib.CategoryTheory.Sites.LocalProperties`; retained the public import
`Sheaf.Paper.DerivedHomMayerVietoris`, which provides `moduleRings` for the statement.
Updated the declaration's proof docstring and its existing DAG node's proof,
proof dependencies and proof origin to match this route.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.sheaf_module_isIso_iff_isIso_over_open_cover`
(node `lem-weil-pbc-sheaf-isomorphism-local-open-cover`).
No holes remain in the item; no holes were added; no intermediate statements
were split off. The proof uses only Mathlib results and the existing abbreviation
`moduleRings`, not any project theorem containing `sorry`.

## No longer needed

Removed proof import `Sheaf.Topology.GlueSheavesOfModules`. Its theorem and node
`lem-weil-pbc-glue-sheaves-of-modules` are no longer proof dependencies of this
item. This is an edge pruned from this item, not a claim that other targets or
modules no longer need the gluing module.

Also removed `def-weil-pbc-module-finite-type-presentation` from this item's
proof dependencies: finite type and finite presentation play no role in the
criterion; restriction is provided directly by Mathlib's `overFunctor`.
The node remains a statement dependency, as in the original statement.
No other imports were removed. The unit `sk-thm-p1` has neither this criterion nor
the gluing theorem among its realized statement or steps; its route is preserved.

## Where the brief, the DAG or earlier work was wrong

The DAG's Mathlib candidate was usable: its several-line specialization closes
the theorem outright. No statement or definition needed repair. The planned
proof via the project's gluing theorem was also implemented and compiled, but
the Mathlib specialization eliminates that outstanding dependency.
The argument uses arbitrary index and module universes as stated, including
empty covers of an empty space; there is no nonempty index assumption.

## Second reading by T3

1. Compared the sole delivered Lean module with the repository using `diff` and
   checked the theorem signature programmatically: it is byte for byte identical.
   No definition or other declaration changed. The differences are the proof,
   its explanatory docstring, and a private proof import. No change record is
   needed. Verdict: pass.
2. Compiled the delivered file locally with `lcompile.py`, without errors or
   warnings. Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.sheaf_module_isIso_iff_isIso_over_open_cover`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. Inspected the
   complete file: no holes, forbidden declarations, or hollow definitions.
   Verdict: pass.
3. No statements were split off and no new declarations or nodes were added.
   Checked the argument for empty covers of the empty space, empty cover members,
   and unrestricted index universes: the cover criterion requires no extra
   nonemptiness assumption. Verdict: pass.
4. Read Mathlib's `Sheaf.isIso_of_coversTop` and the reflection instance for
   `SheafOfModules.toSheaf`; searched module-sheaf and project topology sources
   for cover/restriction isomorphism criteria. The direct specialization already
   takes the short route and needs no project theorem proof. Both remaining
   imports are needed: the public one supplies `moduleRings` in the signature,
   the private one supplies the cover criterion. The report lists both removed
   old proof dependencies. Checked `dag/units/sk-thm-p1.json`: neither pruned
   dependency nor this item realizes a unit step, so its route is preserved.
   Verdict: pass.
5. Compared the node JSON with the repository: only `proof`, `proof_deps`, and
   `proof_origin` changed. The five steps describe the actual Lean proof and
   their dependency union agrees with `proof_deps`. The recorded Lean signature,
   statement, statement dependencies, and unit remain unchanged. Verdict: pass.

Second reading changed only this report; the proof and node needed no repair.
One existing hole is closed, zero holes are added, and zero statements are split
off. Scratch axiom-check files are not delivery modules.
