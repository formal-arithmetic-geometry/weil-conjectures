## What changed

Proved `AlgebraicGeometry.completion_thickening_cokernel_reflection` without changing its
signature. Updated its docstring and node proof to the shorter cokernel-only argument.
Added proof-only imports for coherent cokernel/submodule closure, quasi-coherent tensor
products and cokernels, closed-immersion power quotients and unit kernels, and fully faithful
closed pushforward. The second reading reuses five proved private helpers of CoherentFormalModule through a
proof-only `import all`; three local private helpers remain proved. No auxiliary module was created.

The proof sets Q = coker(a), B = K^s Q. Each reduced cokernel surjects onto the corresponding
quotient of Q. Its annihilation therefore makes every component of completion of B → Q zero.
Faithful completion on the supported coherent category reflects that map as zero. Thus B=0;
power inclusion yields the stated K^(2s) bound. Faithfulness comes from the assumed equivalence
on Z, the existing coherent closed-immersion equivalence and its completion comparison.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.completion_thickening_cokernel_reflection`, node
`lem-weil-pbc-completion-thickening-cokernel-reflection`.

No `sorry` remains in the delivered module. Zero new holes and zero split-off statements.
This is a proof from existing library declarations; their unfinished transitive dependencies
remain work for the project. It is not a claim that the targets' transitive axiom closure is
already sorry-free.

## No longer needed

Removed the unused experimental proof import `Mathlib.CategoryTheory.Equivalence`.
Both public imports support the unchanged signature and
`Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence` supplies the faithful comparison.

Removed these direct proof dependencies from the node:
- `lem-weil-pbc-coherent-formal-cokernel-canonical`, module
  `Sheaf.AlgebraicGeometry.CoherentFormalModulesCokernelCanonical`;
- `lem-weil-pbc-completion-finite-module-tensor`, Mathlib
  `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`;
- `lem-weil-pbc-completion-exact-finite-modules`, Mathlib
  `Mathlib.RingTheory.AdicCompletion.Exactness`.

The formal cokernel construction and affine completed-ring argument are unnecessary here.
`lem-weil-pbc-closed-immersion-pushforward-ideal-powers` is no longer a direct node dependency,
but remains used transitively by the closed-immersion completion comparison; its module is
not claimed globally pruned. Other users may still need every removed dependency above.
The new node proof lists all replacement dependencies. No unit statement or realized unit
step was bypassed; this node is below the unit's realized statements and steps.

Second reading also removed these proof-only imports after reusing existing private lemmas:
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`;
- `Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`;
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`;
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`;
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
The first module's node `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` is also
removed from the original direct proof dependencies. Tensor-product and cokernel closure
nodes remain transitive dependencies of the reused core lemmas, not direct dependencies
of this proof. The core node `def-weil-pbc-coherent-formal-module` records those helpers.
No globally unreachable module is claimed here.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan used preservation of cokernels and ideal-action images by exact
completion. Those results are stronger than this cokernel-only argument needs. Right
exactness of reduction follows directly by factoring its epimorphic quotient maps, and
faithfulness globally on Z reflects the ideal-product inclusion. No local faithfulness of
affine completion is assumed. The proof actually obtains K^s coker(a)=0 before the final
power inclusion. It does not use hF or positivity of q or s, but keeps every binder unchanged.

The cited Stacks source was read at Tags 088A and 087T online because the local source
`literature/stacks-project/coherent.tex` is absent on this machine. No source discrepancy,
interface correction, forced adaptation, or tool workaround was needed.

## Second reading by V2

1. PASS: compared the only delivered module with the repository. The complete existing
   theorem signature is byte for byte identical. No existing definition or public
   visibility changed, no change record is needed, and no other module is delivered.
2. PASS: compiled the original delivery and the repaired module without errors or
   warnings. No `sorry`, forbidden declaration, hollow definition, or arbitrary data
   witness was introduced. A scratch `#print axioms` reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` from existing dependencies. The
   equivalence/comparison witnesses are used locally in proofs, not to define data.
3. PASS: zero split-off statements and zero new nodes. Checked the private reductions:
   tensor right exactness passes annihilation through epis; mono cancellation passes
   it to subobjects; invertible quotient units give support. Zero modules, zero and
   unit ideals, identity/zero maps, and q=s=1 satisfy these arguments. Searched the
   library by ideal-product zero/quotient and faithful-completion terminology and
   Mathlib via msearch grep; found five existing core helpers and reused them.
4. PASS after pruning: the cokernel-only argument is shorter than the old exactness
   route. Reused core power quasi-coherence, image quasi-coherence, mono, quotient
   annihilation, and mono annihilation lemmas. Removed five proof-only imports and
   their unused direct dependencies. Checked sk-thm-p1's `realized` statement and
   every step: this node and the pruned dependencies are not realized unit steps;
   no unit route is bypassed. All old unused proof dependencies are reported above.
5. PASS after synchronization: only node `proof`, `proof_deps`, and `proof_origin`
   changed; their steps and dependency union now match the proof and its reused
   core lemmas. Existing `statement`, `stmt_deps`, and `lean.statement` are unchanged.

Changes in this reading: removed five duplicate local helpers, reused the core's
proved power quasi-coherence lemma, removed five proof-only imports, synchronized
node dependencies and the report. Closed one original hole, added zero holes;
this is a proof from existing dependencies, not a decomposition.
