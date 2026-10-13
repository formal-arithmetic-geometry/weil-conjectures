## What changed

Completed `AlgebraicGeometry.RingedSpace.exists_finiteFree_local_hom_zero` in
`Sheaf.AlgebraicGeometry.FiniteFreeLocalHomZero`, following both steps of
`lem-weil-pbc-finite-free-local-hom-zero` without changing its statement or imports.
The images of the restricted coproduct inclusions evaluated at 1 give finitely many
sections on V. Mathlib's `TopCat.Presheaf.germ_eq` shrinks each to zero; their finite
intersection is open and contains x. Naturality and restriction preserve this vanishing
on every smaller open. Since both restriction functors preserve coproducts, the mapped
free cofan's universal property proves the restricted morphism zero.

A declaration-local `linter.unusedVariables false` suppresses the warning for the
original unused existential proof binder `hxW` in the conclusion. Its signature,
visibility, docstring and all mathematical hypotheses remain unchanged.

Searches used LeanFinder (zero stalk map of a finite free sheaf), Loogle
(`SheafOfModules.free`) and grep (`germ_eq|overMapUnitIso|isColimitFreeCofan`).
They found the germ criterion and free cofan APIs, but no combined theorem.
The Stacks 01CP proof was read at https://stacks.math.columbia.edu/tag/01CP;
the local `literature/stacks-project/modules.tex` is absent on this machine.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.RingedSpace.exists_finiteFree_local_hom_zero`
(node `lem-weil-pbc-finite-free-local-hom-zero`).
No holes remain or were added; no intermediate theorem was split off.

The finite intersection construction also covers an empty I: its infimum is top,
so the chosen neighborhood is V and the empty coproduct hom-ext closes the proof.
Only finiteness of I is used, with no finiteness or nontriviality assumption on G.

## No longer needed

None. All three existing public imports are needed by the unchanged statement:
free sheaves, restriction functors, and `RingedSpace.Modules` respectively.
No new proof imports, nodes or modules were introduced. The existing two-step DAG
route is retained, so no node update or unit-route change is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The standing page refers to a stage-3 section of
`coord/delivery-errors.md`, but this checkout has sections A–H only.
The existing conclusion names an existential proof binder that is never used;
the local linter option avoids altering that signature merely to silence a warning.

## Second reading by N4

1. Compared the delivered module with the repository version. The theorem signature,
visibility, docstring, and imports are unchanged; the only differences are the proof
and a declaration-local linter option for the unused existential binder. Verdict: pass.

2. Compiled `lean/Sheaf/AlgebraicGeometry/FiniteFreeLocalHomZero.lean` with the required
`lcompile.py` command. It compiles without errors or warnings, and the proof contains no
`sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Verdict: pass.

3. Checked the sole declaration against the existing node and searched the library and
Mathlib-facing APIs for duplicate lemmas. No new statement was split off and no duplicate
declaration was introduced. The proof uses the existing germ equality criterion and the
free cofan universal property. Verdict: pass.

4. Read the proof from the target downward. It intersects the neighborhoods obtained for
the finitely many basis sections, proves each restricted basis map zero by naturality,
and invokes preservation of the free cofan colimit. The existing unit route and all
proof dependencies are retained; no imports or nodes can be pruned. Verdict: pass.

5. The node's proof text and dependencies agree with the Lean proof, and the unit's
`realized` route is unchanged. Verdict: pass.

Changed only this report section; no mathematical or interface changes were required.
