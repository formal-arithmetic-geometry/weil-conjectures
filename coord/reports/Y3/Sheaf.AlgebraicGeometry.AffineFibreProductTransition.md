## What changed

Proved `AlgebraicGeometry.isAffineHom_pullback_map` in
`Sheaf.AlgebraicGeometry.AffineFibreProductTransition`, without changing its signature.
Added the proof-only import `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
The proof follows all four steps of the existing node: affine `h` is separated;
`pullback.mapDesc f' g' h` is a closed immersion and hence affine; the fixed-base
comparison `k` is affine by `MorphismProperty.pullbackMap`; projection extensionality
identifies the requested map with their composite, which is affine by composition.
All these constituent results are already proved in Mathlib. No new lemmas are needed.
The node's proof and proof dependencies already describe this exact route, so no
node fields require changes. The unit route is preserved.

Compilation with the required `lcompile.py` wrapper succeeded without warnings.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.isAffineHom_pullback_map`
(node `lem-weil-pbc-fibre-product-affine-transition`).
No holes remain in the module and no holes were added. This is a proof, not a decomposition.

## No longer needed

None. The original public import is needed by the statement, and the added proof-only
import supplies separatedness and the closed immersion of the change-of-base map.
All six existing proof dependencies remain used, through their Mathlib declarations.
No nodes or modules from the existing route are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The planned argument works directly with the Mathlib declarations named in the
nodes. The whole-item Lean Finder search returned affine pullback facts rather than
an exact transition theorem. Reading `Affine.lean`, `Separated.lean`,
`ClosedImmersion.lean`, `MorphismProperty/Limits.lean`, and `HasPullback.lean`
provided the constituent instances, `MorphismProperty.pullbackMap`, and the
projection simplification lemmas used in the proof.

## Second reading by Y3

1. **Interface preservation — pass.** Compared the only delivered module with the
   repository using `diff -u`. The existing theorem signature, universe, visibility,
   docstrings and definitions are byte for byte unchanged. The only Lean changes
   are replacement of its `sorry` and the plain proof-only import of `Separated`.
   No statement change or change record is needed.
2. **Proof and axioms — pass.** Independently compiled the file with `lcompile.py`:
   exit code 0, no warnings. A scratch copy with
   `#print axioms AlgebraicGeometry.isAffineHom_pullback_map` compiled and reported
   exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Scanned
   the delivered Lean source: no `sorry`, forbidden declarations or hollow data.
3. **Split statements — pass (none).** No new declaration, split-off theorem, node
   or unproved witness is introduced. The factorization works for arbitrary
   compatible scheme diagrams, including identity comparisons and empty schemes;
   no extra nonemptiness or affineness of the schemes is used.
4. **Route, imports and pruning — pass.** Read the Mathlib definitions of
   `pullback.map` and `pullback.mapDesc`, `MorphismProperty.pullbackMap`, affine
   composition, affine implies separated, and the closed-immersion/affine instances
   for `mapDesc`. The first factor changes the base via `h`; the second is the
   fixed-base product of `a` and `c`. Projection extensionality identifies their
   composite with the requested map. Independent source searches in Mathlib,
   upstream and `lean/Sheaf` found no exact existing transition theorem. Both
   imports are necessary: `Affine` supplies the public signature and fixed-base
   affineness, while `Separated` supplies the proof's change-of-base instance.
   All six old proof dependencies are used, so `No longer needed: None` is
   complete. Read `dag/units/sk-thm-p1.json`: no realized statement or step is
   bypassed or changed; this proof retains the existing node's full route.
5. **DAG agreement — pass.** Read the item's node and the Lean/Mathlib matches of
   every proof dependency. Its four proof steps, six dependencies and documentary
   proof origin agree with the actual proof, including the instances synthesized
   by the final `infer_instance`. No node edits are required.

Second reading changed only this report by appending the independent review.
The Lean proof is retained unchanged: one original hole closed, zero holes added,
zero split off, no nodes or modules pruned.
