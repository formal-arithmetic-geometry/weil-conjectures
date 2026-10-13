## What changed

Reduced `AlgebraicGeometry.rightAdjointTensorComparison_triangle` without changing its signature
or existing docstring. The original module now proves shift stability of quasi-coherent
cohomology, transports the input triangle to its specified quasi-coherent vertices, constructs
the two mapped triangles and their morphism, and verifies all three vertex formulas.
The connecting-arrow square is proved from `NatTrans.shift_app_comm` and naturality;
the first two squares use naturality directly.

Added one proof-only import, `Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures`.
Its single public statement isolates the geometric construction of simultaneous coherent
exact shift structures and shift compatibility of the pinned comparison. It asserts no
triangle morphism, no vertex isomorphisms, and no component formulas for such a morphism.
The original module supplies that construction in a complete Lean proof.
All existing public imports are retained because the statement uses their definitions.
The parent DAG proof and proof dependencies now match the compiled reduction.

Validation: both sandbox modules compile through `lcompile.py`, with no compiler errors or
non-sorry warnings. The geometric structure statement was checked against zero objects,
zero components, zero triangles, arbitrary integer translations, the unchanged independent
localization universe, and the absence of any assumption that a component of tau is invertible.
No object-valued definition chooses data from an unproved existence theorem.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.rightAdjointTensorComparison_triangle`
(node `lem-sc-right-adjoint-tensor-comparison-triangle`) by a compiling reduction.
There is no sorry left in the assigned module.

Added one hole: `AlgebraicGeometry.rightAdjointTensor_compatibleExactStructures`, in
`Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures`
(node `lem-sc-right-adjoint-tensor-compatible-exact-structures`). Its whole proof is
`by sorry`; its docstring and node describe the remaining geometric argument.

This is a decomposition: one original hole closed and one strictly intermediate hole added,
net zero holes. The geometric comparison is not claimed to be proved without sorry.
The private helpers `qc_shift`, `qc_stable`, and `triangleComparison` are fully proved.

## No longer needed

No existing import was removed. All five original public imports are statement dependencies.
The new module does not import `RightAdjointTensorComparisonNatural` or
`RightAdjointTensorComparisonShift`: the supplied tau and pinned-component hypothesis already
provide the former's input, while a merely existential objectwise shift square from the latter
does not supply the simultaneous coherent shift structures needed on connecting arrows.

Removed the direct proof dependency `lem-sc-right-adjoint-tensor-comparison-natural`
(module `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural`) from the parent node.
Its statement dependency stays, because it identifies the pinned formula in the node's text.
Removed the parent's direct proof dependencies `def-pc-derived-direct-image`,
`def-pc-derived-pullback`, and `def-pc-scheme-derived-tensor-structure`, delegating them
to the new structure node, which retains them. These definitions remain necessary, not globally pruned.
No unit-level statement or proof step is bypassed; `sk-thm-picard-duality` is unchanged.
No globally unreachable module is claimed.

Second reading removed redundant imports `Mathlib.CategoryTheory.ObjectProperty.Shift`
and `Mathlib.CategoryTheory.Triangulated.Functor` from the new module. Its statement
compiles with these APIs supplied by the retained imports; no additional DAG node is pruned.

## Where the brief, the DAG or earlier work was wrong

The parent plan's single step combines two different tasks: constructing compatible exact
structures and transporting triangles. Its proof dependencies are definitions and a theorem
constructing the natural transformation; none states the needed simultaneous geometric exactness
and shift compatibility. The new structure statement makes that implicit obligation explicit.
The existing shift-square theorem alone cannot replace it: its existential comparisons need
not be coherent across morphisms and connecting arrows.

`blueprint_refs.py ancestor` cannot recover this item's ancestor because its creation chain
uses a module name. The new node records `lem-sc-finite-duality` and the explicit intervening
chain, following the already recorded ancestor of the diagrams node. No existing blueprint
field is changed.

The cited local Stacks TeX file is absent on this machine. Read the official source at
[Tag 0A9U](https://stacks.math.columbia.edu/tag/0A9U) and
[Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S).
Tag 0A9U leaves the compatibility implicit in its assertion that the isomorphism locus is
triangulated. The expanded remaining proof is accordingly marked agent-written, not a
verbatim source proof. Perfectness is used by that source for subsequent coproduct and
isomorphism arguments, not added as a hypothesis to this compatibility decomposition.

## New nodes

`lem-sc-right-adjoint-tensor-compatible-exact-structures`:
`dag/nodes/sec-picard-framework/lem-sc-right-adjoint-tensor-compatible-exact-structures.json`.
The coherent shift structures and exactness of both comparison functors, together with
shift compatibility of the pinned transformation, are the part of the parent plan remaining
for the next worker. The ambient inclusion tests whether a triangle is distinguished, so no separate
triangulated-category instance for the quasi-coherent subcategory is postulated.
Three kinds of Mathlib search were actually run; LeanSearch was unavailable, while
LeanFinder, Loogle, and source grep returned only generic infrastructure.
No change record is needed: all existing public signatures and visibility are unchanged.


## Second reading by N3

1. Compared the assigned module with the repository using `diff -u` and extracted the
   existing theorem signature for a byte comparison: identical, including every universe,
   instance, `hRf`, `hO`, `hTensor`, both adjunctions, `tau`, the pinned `hτ`, and all three
   vertex formulas. Its existing docstring is unchanged. Only private helpers, the proof,
   and a plain proof-only import were added; shift stability is installed locally in the proof. The second module and its node are new;
   there are no changes to existing definitions or public visibility. Verdict: pass.

2. Compiled both modules in import order with `lcompile.py --all`. There are no errors
   or non-sorry warnings. Checked scratch copies using `#print axioms` for `qc_shift`,
   `qc_stable`, `triangleComparison`, `rightAdjointTensorComparison_triangle`, and
   `rightAdjointTensor_compatibleExactStructures`. The helpers use only `propext`,
   `Classical.choice`, and `Quot.sound`; the two public theorems additionally use
   `sorryAx`, as reported. The only delivered `sorry` is the new named theorem's entire
   proof. There are no forbidden declarations or hollow definitions. Existential shift
   structures are eliminated inside a proof of a proposition, not used to define data.
   Verdict: pass as a decomposition, not a completed geometric proof.

3. Read the new statement, its docstring, and its node against official Stacks Tags
   [0A9U](https://stacks.math.columbia.edu/tag/0A9U) and
   [0A9S](https://stacks.math.columbia.edu/tag/0A9S). The former implicitly uses triangle
   compatibility of this comparison; the latter pins its map. The new lemma isolates
   exact shift structures and compatibility, without asserting a triangle morphism or
   any vertex formulas. The ambient distinguished-triangle premise avoids assuming an
   unstated triangulated instance on the full subcategory. Checked the zero-object and
   zero-triangle cases, noninvertible components, negative and zero integer shifts,
   arbitrary specified adjunctions, and the independent localization universe. No
   perfectness or invertibility hypothesis was added: perfectness in 0A9U concerns the
   later coproduct/isomorphism argument. The remaining K-flat, right-adjoint exactness,
   and mate computations are genuinely geometric and remain explicitly unproved.
   Independently searched LeanFinder for coherent shift compatibility of the projection
   formula transformation, Loogle for `CategoryTheory.Adjunction.IsTriangulated`, and
   source grep with `projection.*[Ss]hift`, `[Ss]hift.*projection`, `tensorRight`, and
   `mapTriangleHom`. Read Mathlib's `Adjunction.isTriangulated_rightAdjoint` and upstream
   `Adjunction.commShift_rightAdjointProjectionMap_app` and `commShift_projectionMap_app`:
   they require exact/shift structures and comparison compatibility, and do not supply
   this geometric obligation. The generic triangle-isomorphism API assumes invertible
   components and cannot replace `triangleComparison`. No exact duplicate was found in
   Mathlib, the upstream source, or `lean/Sheaf`. Verdict: a strictly intermediate
   geometric obligation; not a renaming of the item and not closable in a few minutes.

4. Read the proof top down: homology shift isomorphisms prove quasi-coherent shift
   stability; the new lemma supplies compatible exact structures; `Triangle.isoMk`
   transports the given triangle to A, B, C; its third arrow explicitly includes the
   shifted first vertex isomorphism and inverse inclusion shift comparison. Exactness
   then supplies the two distinguished images. Naturality proves the first two squares;
   `NatTrans.shift_app_comm` and naturality prove the connecting square. The six reflexive
   vertex isomorphisms give exactly the required formulas. No shorter available theorem
   bypasses the remaining geometric obligation. Removed two redundant public imports
   from the new module after compiling a scratch copy without them. Checked every old
   parent proof dependency against the new list; all four removed direct dependencies
   are listed above, and the three geometric definitions remain indirect dependencies.
   Read `dag/units/sk-thm-picard-duality.json`: its statement, step, and `realized` records
   are unchanged, and this reduction stays within the same duality route. Verdict: pass.

5. Checked both node files: `proof_deps` equals the union of the proof-step `uses` in
   each; the parent steps match the actual shift-stability, structure application,
   triangle transport, and component calculation. The new node records source,
   agent-written proof origin, searches, creation, blueprint ancestry, chapter, unit,
   and Lean declaration. Its sole hole is exactly the one listed in the report.
   Corrected its `lean.statement` to the verbatim multiline Lean signature. Verdict: pass.

Second reading also replaced the private global instance `qc_stable` by a private theorem
and installed its result only as a local instance inside the original theorem proof.
This prevents a new global typeclass registration for downstream modules.

Other second-reading changes are redundant imports in the new module, its module-docstring
blueprint reference, the verbatim signature record of its new node, and this report's
explicit pruning/review details. No existing public signature was changed. One original
hole is closed by reduction and one geometric hole is added: net zero holes, no claim of
an axiom-free proof of the original theorem, and no globally pruned module.
