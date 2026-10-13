## What changed

Proved `AlgebraicGeometry.coherentKernel_idealProduct_completion_zero` in
`Sheaf.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero` without changing
its signature or existing docstring. Added private proved helpers constructing the
section-to-completion map, checking its projections and naturality, transporting the
existing affine quotient-limit dictionary, and proving injectivity of completed inclusions.
All additional imports are proof-only. Updated the existing DAG node to this route.

The proof uses the coherent kernel, its quasi-coherent ideal product and Noetherian
submodule coherence. On an affine open the annihilator kills the canonical completion
image of the ideal product in F. Completed inclusion injectivity kills the canonical
image in the product itself. Surjectivity of each affine quotient projection and sheaf
separatedness then give global quotient vanishing. No completion faithfulness is asserted.

Local single-file compilation passed with no warnings. The delivery dry run also checks
the declarations and axioms. Edge cases t = 0, empty affine opens, zero modules, and
unit or zero completion ideal are covered by the same proof; the zero ideal power
uses the identity inclusion explicitly.

## Proved and sorry left

Closed the single hole:
`AlgebraicGeometry.coherentKernel_idealProduct_completion_zero`
(node `lem-weil-pbc-coherent-kernel-ideal-product-completion-zero`).
No holes remain in this module, and no holes or new public declarations were added.
This is a proof from existing library declarations, not a decomposition.

## No longer needed

Removed the original proof-only import
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`. The original public import of
`Sheaf.AlgebraicGeometry.CoherentFormalModule` is needed by the unchanged statement.
No unused experimental import remains.

The following original direct proof dependencies are pruned from this node's route:

- `lem-weil-pbc-coherent-formal-modules-affine`, module
  `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`: the existing direct
  affine quotient-limit comparison suffices; no equivalence of formal categories is used.
- `lem-weil-pbc-completion-finite-module-tensor`, Mathlib
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` and related declarations:
  injectivity of completed inclusions suffices.
- `lem-weil-pbc-noetherian-completion-flat`, Mathlib
  `AdicCompletion.flat_of_isNoetherian`: not needed for the chosen argument.

These are local dependency prunings; no claim is made that other target branches
or imported modules never use these facts.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan asks for more completion theory than
needed: equality with the completed kernel and tensor-product flatness can be replaced
by naturality of the canonical section-to-limit map and injectivity of the completed
inclusion into F. The unit route is unchanged; this node is below the unit level.

## Second reading by R4

1. Compared the delivered module with the repository module: the sole existing
   declaration's signature is byte for byte identical, and its docstring and public
   import are unchanged. All added helpers are private; no existing definition or
   interface changes. Verdict: pass.
2. Read the entire proof and its helpers and compiled the module with lcompile.py
   without errors or warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.coherentKernel_idealProduct_completion_zero` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. There is no local sorry,
   forbidden declaration or hollow definition. The sole new definition constructs
   the limit map explicitly from canonical quotient projections. The comparison
   witnesses come from a proved theorem and their projection equations determine
   the maps uniquely. Verdict: pass.
3. No statements were split off and no holes were added. The private proved helpers
   check the canonical map, its naturality and affine completed-inclusion injectivity.
   Reviewed t=0 (identity ideal inclusion), empty affines and schemes, zero modules,
   I=0 (constant quotients), and I=1 (zero quotients). None requires completion
   faithfulness. Verdict: pass; there are no split statements to repair.
4. Repeated the search with Loogle `AdicCompletion.map, Function.Injective`, which
   finds the exact Mathlib `AdicCompletion.map_injective` used here. Searched both
   Lean roots for completion units, naturality and injectivity and read the existing
   affine natural comparison: it needs the larger formal-category realization and
   is still sorry, so it gives no shorter proved route. Each imported module supplies
   a used theorem or private helper; the `import all` declarations are proof-only
   access to those helpers. The old proof dependency set loses exactly the three
   nodes listed above. Read `dag/units/sk-thm-p1.json`: this item and these pruned
   auxiliary nodes do not realize a unit statement or step; the realized route is
   kept. Verdict: pass.
5. Compared the old and delivered node. Only proof, proof_deps and proof_origin
   change; the four steps follow the actual Lean proof, and proof_deps is the union
   of their uses. Completion injectivity is correctly represented by the existing
   Mathlib exact-finite-modules node. No new nodes or change records are needed.
   Verdict: pass.

Changed the report to identify the removed original proof-only import
`Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine`; the previous claim that no
original import was removed was incorrect. No Lean repair was necessary. The
unchanged original docstring describes the longer tensor-flatness route; the actual
shorter injectivity route is documented in this report and the updated DAG proof.
