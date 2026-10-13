## What changed

Proved `LinearMap.exists_ideal_power_hom_lift` in
`Sheaf.RingTheory.IdealPowerHomLift` without changing its signature or visibility.
A proved private finite-cycle helper constructs the difference map, its kernel,
the principal-cycle map and the quotient homology. Two uses of Mathlib flat
exactness and the existing torsion-module comparison lift the cycle modulo a
principal cycle. The main proof checks relation images directly using the existing
torsion-submodule comparison, then factors through the surjective linear-combination
map using Mathlib's quotient-kernel equivalence.

Replaced the proof import `Sheaf.RingTheory.TorsionHomFlatComparison` with
`Sheaf.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso`. Added proof imports
`Mathlib.RingTheory.Finiteness.Ideal`,
`Mathlib.LinearAlgebra.Finsupp.LinearCombination`, and
`Mathlib.LinearAlgebra.Isomorphisms`. All existing public imports remain.
Updated the item's DAG proof, proof dependencies and proof origin to match the
coordinate argument. No other module or interface was changed.

## Proved and sorry left

Closed the single original hole: `LinearMap.exists_ideal_power_hom_lift`
(node `lem-weil-pbc-ideal-power-hom-lift`). The private helper
`LinearMap.exists_finite_koszul_cycle_lift` is also proved.
No `sorry` remains in the delivered module; no new holes or modules were added.
Both parts and their combination compile through `lcompile.py` without warnings.
The argument handles empty generators and zero/unit ideals uniformly.

## No longer needed

Removed import `Sheaf.RingTheory.TorsionHomFlatComparison`, with dependency node
`lem-weil-pbc-torsion-hom-flat-comparison`. The naive free-module quotient and its
kernel are not constructed: `def-weil-pbc-free-module` is no longer a proof dependency.
Removed `lem-weil-pbc-tensor-right-exact` from this node's dependencies: the two exact
sequences are both handled by `Module.Flat.lTensor_exact`, already available under
the flatness assumption. These are local pruning decisions; the modules/nodes may
still be needed elsewhere in the targets' closure.
Retained `Mathlib.LinearAlgebra.TensorProduct.Pi` for the finite-cycle calculation
and `Sheaf.Paper.TorsionModuleFlatBaseChangeIso` for its homology quotient.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature correction was needed. The original plan is valid,
but its use of the full torsion-source Hom comparison is avoidable: each relation's
image is itself killed by the ideal power, and 05EC(1) injectivity suffices.
The source TeX file named by the node is absent on this machine; the official Stacks
pages for 05ED, 05EF and 05EG were read to verify the source argument.
The unit `sk-thm-p1` route and all realized unit statements/steps are unchanged.

## Second reading by U1

1. I compared the delivered module with the repository version. The public theorem signature and all existing declarations are byte for byte unchanged; only proof code and proof-only imports were changed. Verdict: pass.
2. I compiled the module with `lcompile.py`; it succeeds without errors or warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and the helper is a proved private theorem. Verdict: pass.
3. The private finite-cycle lemma is a genuine intermediate reduction, not a restatement of the target. Its construction handles empty generators and the edge cases of zero and unit ideals. The relation-kernel argument uses the existing torsion-submodule comparison, and no duplicate library theorem was found. Verdict: pass.
4. The proof proceeds from finite generators through explicit Koszul cycles, flat exactness, torsion comparison, and quotient descent. The route keeps the unit `sk-thm-p1`; removed proof dependencies are reflected in the node. Verdict: pass.
5. The DAG proof, dependencies, and origin match the Lean proof, including the switch to the torsion-submodule comparison. Verdict: pass.

I changed only this second-reading report section; no Lean declarations, statements, or DAG data were changed during the review.
