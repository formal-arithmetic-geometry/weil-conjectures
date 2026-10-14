## What changed

Proved `AlgebraicGeometry.schemeCanonicalTensorUnit_component` in
`lean/Sheaf/AlgebraicGeometry/SchemeCanonicalTensorUnitComponent.lean`, keeping its
signature and existing docstring unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationGradedAugmentation`.

The proof first identifies every component of the supplied map `e` with the
explicit graded evaluation by applying the already-proved augmentation identity
and cancelling the degreewise monic K-injective augmentation. It then calculates
the total tensor action with Mathlib's associator and tensor-map inclusion
formulas. In degree zero, a right-unitor inclusion formula follows from the
explicit inverse unitor; in other degrees the single coefficient object is zero.
Tensor-Hom naturality moves `singleObjXSelf` inside the inverse adjunction.
Composition with the augmentation of `F` finishes the stated equality.

Five private helpers prove these calculations for abstract complexes or an
abstract projection morphism. They have complete Lean proofs and introduce no
new definitions or public statements. Abstracting the projections avoids
expensive reduction of their chosen existence specification. The unchanged
60-second compiler limit is used; the increased heartbeat allowance has its
required explanatory comment.

Updated the existing node's `proof`, `proof_deps` and `proof_origin` to record
reuse of `lem-pc-scheme-ordinary-evaluation-graded-augmentation`.

Searches: LeanFinder found the standard complex right unitor and associator
APIs; Loogle and grep found the summand and inverse-unitor formulas. Source
searches found the proved graded augmentation identity. No combined theorem
already proved the requested statement. The cited Stacks material was read at
[08DJ](https://stacks.math.columbia.edu/tag/08DJ),
[08DM](https://stacks.math.columbia.edu/tag/08DM), and
[08DQ](https://stacks.math.columbia.edu/tag/08DQ); the local literature text is
absent on this machine. The unit record `sk-thm-picard-duality` has no realized
statement or proof-step nodes to bypass; its route is unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.schemeCanonicalTensorUnit_component`
(`lem-pc-scheme-canonical-tensor-unit-component`), the module's only original
`sorry`.

Added holes: none. Remaining holes in the delivered module: none. Split-offs:
none. All five private helpers are proved. No other modules are changed.

## No longer needed

No imports were removed and no modules become unreachable through this change.
The three original public imports remain necessary for the theorem's signature.
The differential compatibility theorem
`lem-pc-tensor-hom-uncurry-differential` is no longer a direct proof dependency:
its component naturality portion is reused through the already-proved graded
augmentation lemma. Its module remains publicly imported because the statement
uses `schemeTensorHomUncurry`. The direct proof dependencies now consist of the
tensor action definition, tensor-closed structure, Hom projections, and graded
augmentation identity. No claim of module pruning is made.

## Where the brief, the DAG or earlier work was wrong

The planned coefficient cancellation and tensor action calculation are valid.
No signature, definition or mathematical correction was needed. The coefficient
naturality argument already existed in the proved graded augmentation lemma;
repeating it with the concrete chosen projections caused expensive reductions.
The final proof uses abstract, proved helpers instead. The calculations are
uniform over all integer degrees and arbitrary complexes, including zero
complexes and the empty scheme; they add no boundedness, flatness or existence
hypothesis.


## Second reading by R3

1. **Public contract — pass.** Compared the sole delivered module with the
   repository using `diff`. The existing theorem signature and docstring are
   byte-for-byte identical. No definition, existing visibility, public import,
   or target statement changed. The only added import is proof-only. There are
   no additional delivered modules or change records.

2. **Kernel proof — pass.** Compiled the delivered file through `lcompile.py`
   without errors or warnings (58.9 seconds). Independently compiled a scratch
   copy containing `#print axioms` for all five private helpers and
   `AlgebraicGeometry.schemeCanonicalTensorUnit_component` (53.6 seconds).
   Every declaration uses exactly `propext`, `Classical.choice`, and
   `Quot.sound`; none uses `sorryAx`. Scanned the source: no `sorry`, forbidden
   declaration, implementation escape, hollow definition, or overlong line.
   The proof constructs no data from an unproved existence statement.

3. **Split statements and small cases — pass.** There are no new public
   statements, new nodes, or split-off holes. Read each private helper:
   associator and tensor-map naturality give the triple summand, inverse-unitor
   cancellation gives the degree-zero summand, and zero target components give
   the remaining degrees. The integer equations imply `p = k` only in the
   branch `r + q = 0`; no nonnegativity assumption is used. Degree zero,
   negative degrees, zero complexes, and the empty scheme introduce no excluded
   case. The coefficient calculation uses inverse tensor-Hom naturality with
   the same chosen projections as the unchanged statement.

4. **Route and pruning — pass.** Read the imported graded augmentation proof,
   tensor-unit action construction, and Hom projection interface. Repeated
   searches with different words using LeanFinder, Loogle, and source `rg`
   found the standard complex associator, tensor inclusion and inverse-unitor
   APIs already used, not a shorter combined theorem. The upstream dual-complex
   unit calculation requires additional bounded dual data and does not replace
   this argument. All three existing public imports supply names in the
   signature; the added ordinary-evaluation import supplies the augmentation
   theorem and explicit graded evaluation used in the proof. `No longer
   needed` names the only old direct dependency removed,
   `lem-pc-tensor-hom-uncurry-differential`; its module stays necessary for the
   statement. The unit `sk-thm-picard-duality` has empty realized statement and
   step lists, and this proof changes no unit route or realization. No module
   pruning is claimed.

5. **DAG agreement — pass.** Parsed and compared the old and delivered node.
   Only `proof`, `proof_deps`, and `proof_origin` change. The union of proof-step
   citations equals `proof_deps`. The recorded Lean statement matches the
   unchanged signature. The three proof steps match augmentation cancellation,
   evaluation summand postcomposition, and tensor-action normalization in the
   Lean proof. There are no new nodes to audit.

Second reading changed only this report: added the independent review and its
compiler/axiom evidence. No proof repair was necessary. Closed one original
hole, added zero holes, split off zero statements, and pruned zero modules.
