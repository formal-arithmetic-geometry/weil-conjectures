## What changed

Completed `AlgebraicGeometry.localEvaluationDegreeMap_comm` by tensor-coproduct
and Hom-product extensionality, using the existing degree-map component formula.
Added a proof-only import of `OrdinaryEvaluationDifferentialSummand`, which states
the remaining calculation on one tensor summand and one Hom projection.
Existing signatures and definitions are unchanged. Updated the parent node proof route.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.localEvaluationDegreeMap_comm`.
Added one hole, `AlgebraicGeometry.ordinaryEvaluation_differential_summand`
(lem-pc-ordinary-evaluation-differential-summand), in its own new module.
This is a decomposition, with net zero holes: global assembly is complete but
its component sign calculation remains to be proved. No sorry remains in the item module.

## No longer needed

No existing imports removed and no existing dependency modules pruned.
The parent proof_deps no longer directly lists `def-pc-tensor-complex-sheaves`,
`def-pur-hom-complex`, or `lem-pc-sheaf-modules-tensor-closed`: the component
calculation now belongs to the summand node. Tensor and tensor-Hom constructions
remain its dependencies; the Hom differential is exposed by
`lem-sc-hom-complex-projections`. These modules remain in the import closure;
this delivery claims no pruning of them. The earlier
sandbox's projected whole-source lemma and malformed projection node are removed;
the new statement restricts both the source summand and the target projection.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left a lemma in the item module and did not complete the required
reduction or provide the required node metadata. It also made its projected lemma
proof depend on its parent differential theorem. The replacement has no such cycle:
its proof dependencies are the component definition, differential constructions,
and tensor-Hom naturality. Zero terms and empty opens need no extra hypotheses.
The unit route is preserved. Generic HomTensorDifferential describes currying in
two inputs and does not directly identify this ordinary evaluation construction.

## New nodes

`lem-pc-ordinary-evaluation-differential-summand` in
`Sheaf.AlgebraicGeometry.OrdinaryEvaluationDifferentialSummand` isolates the
Koszul calculation on one tensor summand and one Hom projection. The theorem
applies to graded maps with the stated ordinary component formula, without
perfectness, boundedness or affineness. The main module supplies this hypothesis
using its already proved component formula and assembles the result in Lean.


## Second reading by M1

1. Compared the complete item module with the repository using diff. PASS:
   the only changes are the proof-only summand import and the body of
   `AlgebraicGeometry.localEvaluationDegreeMap_comm`. Every existing signature,
   definition, option and public import is byte-for-byte unchanged. The second
   module is new; no change record or forced adaptation is needed.
2. Compiled both modules in dependency order with lcompile.py. PASS: no errors
   or unexpected warnings. The only new sorry is the named public summand theorem;
   there are no new data definitions or prohibited declarations. A scratch copy
   with #print axioms checks the item's six declarations and the new theorem;
   only the three standard axioms and sorryAx occur. The latter remains through
   the reported component hole; the five construction/formula declarations use
   only the three standard axioms.
3. Read the component definition, the Hom projection differential formula,
   and the complete new theorem and docstring. PASS as a decomposition:
   restricting the source and target leaves precisely one component calculation,
   while the parent contains the actual two extensionality arguments. Checked
   r+q=0, r+q=-1 and the remaining indices: the first yields the d_F term;
   the second yields -(-1)^(p+q) on both sides; the others vanish. Zero complexes,
   empty opens, unbounded complexes and negative degrees require no extra
   hypotheses. The formula hypothesis is supplied by an already proved theorem.
   Searched again using counit/Leibniz/total-tensor terminology with leanfinder,
   loogle and local rg. Mathlib HomComplex cochain differential rules concern
   groups of cochains, not this internal sheaf Hom object. The upstream termwise
   dual evaluation assumes dualizable terms; generic HomTensorDifferential
   curries iterated Hom rather than identifying the specified evaluation map.
   No existing theorem closes this calculation in a few minutes.
4. PASS: the parent takes the direct product/coproduct universal-property route.
   Its public imports support the pre-existing constructions and reexports;
   the added import is proof-only. The summand's public import supplies the
   types and component definitions in its statement. Expanded No longer needed
   to name all three removed direct parent proof dependencies and distinguish
   their relocation from actual module pruning. The unit realized record is
   {statement: [], steps: [[]]}; no realized unit node is bypassed or changed.
5. PASS: read both node records against the Lean, including the new declaration's
   signature, source, complete proof in words, searches, creation metadata and
   blueprint origin. The parent records the component formula and extensionality
   assembly; the new node records only the remaining summand calculation and has
   no dependency on the parent, so no proof cycle is introduced.

Second reading changed reporting only: completed the removed-dependency inventory
and recorded the independent checks. Lean and node files required no repair.
The result remains a decomposition: one original hole closed, one lower hole added,
net zero holes, and no modules pruned.
