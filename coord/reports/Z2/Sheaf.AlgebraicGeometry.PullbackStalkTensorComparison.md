## What changed

Only Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison is changed.
AlgebraicGeometry.PullbackStalkTensor.tensorToStalk: old Classical.choose of
exists_tensorToStalk -> new Algebra.TensorProduct.lift of the explicit projection
stalk algebra homomorphisms, followed by toRingHom. The scalar structure on C is
the actual composite through the left stalk. Its right scalar compatibility is
proved from pullback.condition, with the correct point transport.

Added stalk_square, stalkAlgebra, leftStalkHom, rightStalkHom_commutes,
rightStalkHom, tensorToStalk_tmul, tensorToStalk_spec and tensorToStalk_unique.
The former existence theorem keeps its full statement and is now proved using the
real map; no statement is restated or weakened. All imports remain as on the base.
The existing node def-pc-pullback-stalk-tensor-comparison records the explicit
construction, proof route and added declarations, without a TeX statement change.
Change record: coord/changes/pullback-stalk-tensor-real-map.md.

The downstream scan finds no external textual use of tensorToStalk. Thus no
adapted modules are needed. Transitive users are listed in the change record.
The local Lean check of the final module compiles cleanly in 3.5 seconds.
LeanFinder and Loogle both located Algebra.TensorProduct.lift; the recorded grep
found the same real construction. The new formula and uniqueness lemmas verify
that the map is exactly the intended canonical map, including zero tensors and
unit factors; no flatness, nonempty-point family or nonzero-ring assumption is added.

## Proved and sorry left

Proved both original sorries (2 of 2):
AlgebraicGeometry.PullbackStalkTensor.point_eq and
AlgebraicGeometry.PullbackStalkTensor.exists_tensorToStalk.
Also proved AlgebraicGeometry.PullbackStalkTensor.stalk_square,
AlgebraicGeometry.PullbackStalkTensor.rightStalkHom_commutes,
AlgebraicGeometry.PullbackStalkTensor.tensorToStalk_tmul,
AlgebraicGeometry.PullbackStalkTensor.tensorToStalk_spec and
AlgebraicGeometry.PullbackStalkTensor.tensorToStalk_unique.
All are recorded under def-pc-pullback-stalk-tensor-comparison.
No sorry remains in the item; no sorry or new node is added elsewhere.
Inherited dependencies of the derived cohomology model remain outside this repair.

## No longer needed

No imports, nodes or modules pruned. The defining dependency on an unproved
existential choice disappears: exists_tensorToStalk is now a consequence of the
explicit map, not a source of its data. No new module imports are needed.

## Where the brief, the DAG or earlier work was wrong

The former definition selected unknown map data from an unproved existence
statement. This violated the human's strengthened 2026-10-12 ruling on hollow
definitions. The repaired definition supplies explicit data, with all Prop-valued
obligations proved. The existing mathematical statement and the unit route are
unchanged. The auxiliary existence theorem is retained as a proved compatibility
API, rather than deleted, so callers require no adaptation.

## Second reading by Z2

1. Compared the complete Lean diff against the repository and checked it with
   stage3_delivery.diff_module: no existing declaration signature changed;
   both original sorries are closed and no sorry is added. The sole existing
   definition body changed is tensorToStalk, as declared in the change record.
   No target or other module is modified. Verdict: pass.
2. Compiled the complete delivery with lcompile.py --all, without errors or
   warnings (5.0 seconds). A scratch copy with #print axioms checks the point
   equality, stalk square, explicit algebra structures and homomorphisms,
   tensorToStalk, its formula, restrictions, uniqueness and existence, and
   tensorAlgebra: all use only propext, Classical.choice and Quot.sound.
   The unchanged later stalkTensorComplex, cohomologyModel and IsComparisonIso
   have inherited sorryAx dependencies; these are not introduced by this repair.
   No sorry, forbidden declaration or choice of unproved data occurs in this
   module. The point transport has the correct direction, and the scalar square
   follows from the actual equality of the pullback composites. Verdict: pass.
3. No statement is split off. Read all new compatibility statements: they are
   direct consequences of the actual stalk maps and tensor-product lift, with
   source, blueprint reference and proof explanations. The pure-tensor formula
   and the restriction equations cover zero and unit factors without nonzero,
   flatness or extra point assumptions. An independent LeanFinder search for
   determination by the two factor restrictions returned tensor-product
   extensionality results; the proof already uses Mathlib ringHom_ext. Searched
   both library roots for stalk/tensor-map variants: no existing real definition
   duplicates this one. Verdict: pass.
4. The construction follows the shortest universal-property route, using
   Mathlib stalkMap_congr_hom/stalkMap_comp and TensorProduct.lift/ringHom_ext.
   Imports support the retained derived pullback, module stalk, derived tensor,
   tensor algebra and Tor signatures/instances; none is added solely for a proof.
   The old proof_deps list was empty, so no old dependency is omitted from
   No longer needed. The unit realized record is untouched and no unit route
   is bypassed. Re-ran downstream.py --uses tensorToStalk: no external textual
   users, hence no adaptations. The change record lists the transitive users
   and requests target-definition review. Verdict: pass.
5. Read the node diff with the Lean code open. Its proof steps describe exactly
   the point equality, transported stalk square, scalar compatibility, explicit
   lift, restrictions and uniqueness. The lean record lists the added helpers;
   the original TeX statement and IsComparisonIso signature are unchanged.
   No statement_change or new split node is required. Verdict: pass.

Second reading changed only this report: the construction and proofs needed no
repair. Adapted modules: none.
