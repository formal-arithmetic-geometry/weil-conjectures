## What changed

Proved `AlgebraicGeometry.Scheme.finite_local_cyclic_module_forget_iff` with its signature
unchanged. Added the proved module `Sheaf.AlgebraicGeometry.CyclicModuleConstantReflection`
with `cyclic_module_isConstant_of_forget`. It uses the cokernel of n on a constant abelian
value to reflect constancy without requiring a nonempty scheme or finite values.

The main proof restricts the abelian cover to its nonempty members, reflects constancy,
chooses constant module values, and identifies their underlying groups with finite stalks
at algebraic closures of residue fields. Conversely it forgets each finite trivialization
and lifts geometric points through the cover to identify every stalk with a finite value.
Private helpers explicitly compose the slice-site equivalence, pullback-stalk isomorphism,
and constant-stalk isomorphism. Both modules compile cleanly with lcompile.py.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.finite_local_cyclic_module_forget_iff` (the sole original
hole). Added and proved: `AlgebraicGeometry.Scheme.cyclic_module_isConstant_of_forget`
(node `lem-weil-pbc-cyclic-module-constant-reflection`). No sorry remains in either module;
no holes were split off or added. This is a proof, not a decomposition into holed statements.

## No longer needed

Removed proof imports `Sheaf.Paper.SheavesKilledByNZmodModules`,
`Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`, and the redundant explicit
`WeilConjectures.ConstructibleSheaf.Defs` import. The public imports are preserved.
The node `lem-weil-pbc-sheaves-killed-by-n-zmod-modules` and its module are not used: the
proof works directly with ModuleCat-valued sheaves rather than SheafOfModules over a
constant ring sheaf. The constant geometric stalk fact is retained mathematically through
the proved general `sheafFiberConstantSheafIso` imported from
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`, so its DAG node stays.
The geometric point lift and constant-module forgetting nodes stay as Mathlib leaves.
No unit statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned annihilation test on a chosen abelian constant value is unnecessary. Use
E/nE before lifting scalars; constant sheaves preserve cokernels and the underlying module
sheaf is killed by n, so the resulting constant abelian sheaf is still the original one.
This also handles empty members for reflection of constancy. Nonempty members are needed
only when transferring finiteness from a chosen geometric stalk to a constant value.
The stated SheafOfModules equivalence is a different encoding from the ModuleCat-valued
sheaves here and is therefore pruned.

Read Stacks Definitions 03RU and 03RW in the local etale-cohomology.tex source copy;
the quotient argument is agent-written. Checked edge cases: n=1 gives a zero cokernel
value; an empty base requires no geometric point or nonempty member; disconnected bases
need no fullness assumption on the constant sheaf functor. Mathlib's
`Sheaf.isConstant_of_forget` requires that extra fullness, so it is not applied.
LeanFinder and Loogle found no exact applicable comparison. LeanSearch returned HTTP 500
and is recorded as unavailable. Grep located the cokernel and ZMod action APIs used.
Blueprint searches for cyclic, constant, and constancy found no identical reflection node.

## New nodes

`lem-weil-pbc-cyclic-module-constant-reflection`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-cyclic-module-constant-reflection.json`,
records the completely proved constancy-reflection theorem. It imposes no stalk finiteness
and asserts no cover or finiteness conclusion, hence is strictly smaller than the item.
The parent node's proof, proof dependencies, and proof origin now follow the Lean proof.

## Second reading by V3

1. Compared both delivered modules with the repository. The existing theorem signature
   is byte-for-byte identical; its existing docstring and public imports are unchanged.
   The only new public declaration is the separately stated constancy-reflection theorem.
   No definition or target statement is changed. Verdict: pass.
2. Compiled both modules in import order with lcompile.py, without errors or warnings.
   There are no sorrys or forbidden declarations. Explicit scratch-copy `#print axioms`
   checks for both public theorems report exactly propext, Classical.choice, Quot.sound.
   The private helpers compose genuine isomorphisms. Q is a constructed cokernel, and
   its cyclic action is obtained from the proved annihilation property, not from an
   unproved existence statement. Verdict: pass.
3. No holed statements were split off. Read the complete new reflection proof and its
   docstring: fullness follows from integer lifts; cokernel surjectivity proves nQ=0;
   preservation of cokernels makes the constant quotient projection invertible; full
   faithful forgetting lifts the resulting isomorphism. Checked n=1, empty schemes,
   and disconnected schemes. Independent LeanFinder, Loogle, and grep searches using
   annihilation/constancy/forgetting wording found no applicable duplicate. The existing
   Mathlib reflection lemma requires full constant-sheaf functors, unavailable here.
   Verdict: pass.
4. The target proof follows the finite-value/stalk comparison directly, using proved
   upstream stalk and pullback isomorphisms. Restricting the cover to nonempty members
   preserves surjectivity and justifies residue-field point choices. Proof-only imports
   are plain imports, and the retained imports support the proof or existing signatures.
   The sole removed old proof dependency is the killed-sheaf equivalence, explicitly
   listed above; the other old dependencies remain as Mathlib/upstream facts. Inspected
   sk-thm-p1.realized: neither this node nor the pruned dependency realizes a unit step,
   and the unit route is preserved. Verdict: pass.
5. Read both DAG nodes and compared their proof steps, dependency unions, source records,
   and Lean signatures with the code. The new node contains all required fields and is
   strictly smaller than the finite local comparison, without finiteness or cover claims.
   The parent node records both directions and the explicit stalk transports. Verdict: pass.

Second reading changed only this report, adding the independent review and its validation
results. No Lean proof, statement, definition, import, or DAG repair was needed.
