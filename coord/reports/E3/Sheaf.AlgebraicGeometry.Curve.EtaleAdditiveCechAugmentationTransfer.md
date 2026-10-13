## What changed
The existing target signature and its original docstring are restored verbatim from the
repository. Its proof now sets the required target cohomology class x, lifts
(cY.globalEquiv n).symm x through the surjective homologyπ of the target global
complex, proves the class equation by apply_symm_apply, and applies the remaining
prescribed-class augmentation compatibility theorem to obtain the two total cycles.
The chosen global cycle comes from a proved Mathlib surjectivity theorem, not from an
unproved existence assertion, and no definition is added.

Removed the first worker's two unpublished core theorems and their nodes. Replaced
both by `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechAugmentationPrescribedClass`,
a new module containing the one geometric compatibility obligation. Its global
cycle and correct class equation are supplied as hypotheses; its conclusion only
constructs the two total augmentation witnesses with equal total classes. This
isolates the geometric part from the fully proved quotient-representative argument.
The main module imports this new module privately for its proof. Its two public
imports are unchanged. The canonical transfer import moves into the new obligation
module, where the documented proof uses it.

## Proved and sorry left
Closed the original hole
`AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_augmentation_transfer`.
The class-representative selection and its class equation are proved directly using
`AddCommGrpCat.epi_iff_surjective`, `HomologicalComplex.instEpiHomologyπ`, and the
inverse identity of the supplied additive equivalence.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.etaleAdditiveCech_augmentation_prescribed_class`,
node `lem-pbc-etale-additive-cech-augmentation-prescribed-class`, in the new module.
This is a decomposition: one original hole closed, one lower obligation added,
net zero holes in the import closure. The item still depends on sorryAx; this is
not an unconditional proof of augmentation transfer. The original sandbox's
`etaleAdditiveCech_augmentation_transfer_core_exists` and
`etaleAdditiveCech_augmentation_transfer_core_class` holes were removed before
publication, not closed by proofs.

## No longer needed
No old library module is pruned. The main node no longer directly uses
`lem-weil-pbc-etale-resolution-section-canonical-transfer`; it remains needed by
the new geometric obligation and its module remains in the import closure.
The main module's direct canonical-transfer import is replaced by the private
prescribed-class import. `def-pbc-etale-additive-cech-normalization` remains used
by the representative argument and by the new obligation.

The two unpublished core nodes and declarations are no longer needed and are
removed from the delivery. The unit `sk-thm-p1` and its `realized` fields are
unchanged; this decomposition is below the unit level.

## Where the brief, the DAG or earlier work was wrong
The first split's core-class statement is false without a cover: it asserted the
correct global class for EVERY target cycle satisfying the total augmentation
conditions. Take an empty index type, n=0, g the identity of Spec(Q), source global
cycle of class zero, and target global cycle representing the nonzero constant
section 1. Both Cech totals are zero; all augmentation conditions hold. The
purported class conclusion equates 1 with 0. This counterexample is a mathematical
edge-case check, not a separately formalized Lean refutation. The faulty unpublished
statement is removed rather than left as a dependency or silently weakened.

Both new core DAG nodes also cited the original target as their proof dependency,
creating a cycle. Their natural-language statements were not self-contained and
their docstrings did not explain the missing constructions. The report also
presented the decomposition as a proof. All these faults are repaired here.

Read Stacks Tag 01FD, Lemma 20.15.1, its proof's double-complex diagram, and Tag
01F8, Lemma 20.14.1. The statement of 01FD assumes coverings; the new docstring
explicitly gives the no-cover extension needed here by a direct comparison map
and boundary argument, without inverting an augmentation. It does not apply the
covering theorem to a non-cover. The original target statement is unchanged.

## New nodes
`lem-pbc-etale-additive-cech-augmentation-prescribed-class`: for a supplied target
global cycle with the correct pulled-back cohomology class, construct its total
alpha cycle and the target coefficient beta cycle with equal homology classes.
Its source is the explicit double-complex construction of Stacks Tag 01FD,
with resolution comparisons and coefficient-section identification; its complete
proof in words is in its docstring and node. No proof dependency points back to
the original item. Its Lean record is verbatim from the new module.

Independent searches were actually run through msearch: LeanFinder for refinement
naturality of augmented double complexes (generic resolution-comparison lemmas),
Loogle for homologyπ and Epi (the generic epi instance used by the actual proof),
and Mathlib grep for Cech refinement/naturality and homology naturality. LeanSearch
returned HTTP 500 and is recorded unavailable. Repository and upstream rg searches
found Cech coefficient naturality and generic section-transfer declarations, but
no theorem for the prescribed global class and these total augmentations without
a covering hypothesis. Whole-blueprint searches for augmentation and Cech found
no duplicate of this compatibility statement. No change record is necessary:
no published signature or definition is changed.

## Second reading by E3
1. Compared the delivered target module with the repository using diff and an exact
   signature assertion: the existing target signature is byte-for-byte identical,
   its original docstring is restored, and both public imports stay the same.
   No published definition or statement changes. Only the target proof, a private
   proof import, new module/node, and proof fields of the original node change.
2. Compiled the original worker's module successfully but rejected its mathematical
   dependency. Compiled both repaired modules in import order with lcompile.py.
   There is exactly one new named theorem with `:= by sorry`, the prescribed-class
   compatibility obligation; no definition contains sorry and no forbidden escape
   mechanism occurs. Axiom probes and the delivery checks are recorded below.
3. Tested empty indices, empty schemes/intersections, degree zero, and identity
   morphisms. The first worker's universal class conclusion fails the empty-index
   test above. In the replacement, hclass is a necessary supplied equation, not
   inferred from a non-cover's total complex. The documented chain-map and boundary
   argument proves exactly the residual augmentation assertion. The global cycle
   is fixed in advance; neither its existence nor its class equality is deferred.
   The independent searches are described under New nodes. No duplicate was found.
4. Used the shortest algebraic route for the class-representative component: the
   target canonical equivalence and Mathlib's epi quotient. Geometric transfer
   compatibility remains open and is honestly reported as a decomposition. No
   target-reached old module is lost. The complete list of old proof dependencies
   no longer directly used is recorded above. The Artin-Schreier route of
   sk-thm-p1 and every realized binding are kept.
5. The original node now records the two actual proof steps: representative
   selection and residual compatibility. The new node has a self-contained
   statement, a complete argument, real search records, source, creator, blueprint
   ancestry, unit/chapter, and the exact Lean signature. The dependency cycle in
   the first split is removed. Its remaining dependencies are the same lower
   normalization/canonical-transfer nodes used by the original geometric plan.

Changed: removed the false universal class lemma and the circular unpublished split;
restored the target docstring; proved class selection with Mathlib; left one precise
geometric compatibility obligation in its own module; corrected DAG and reporting.

Axiom probes of both delivered theorems compiled: each lists only propext,
Classical.choice, Quot.sound, and sorryAx. The residual obligation accounts for
the allowed open-proof axiom; no additional axiom was found. The temporary probe
is absent. Both delivered module files compile cleanly in import order.
