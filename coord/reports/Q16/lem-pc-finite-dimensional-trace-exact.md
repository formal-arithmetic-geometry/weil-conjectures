# Q16: lem-pc-finite-dimensional-trace-exact

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-finite-dimensional-trace-exact.json`: existing statement, now split into five steps; no new nodes and no new Mathlib leaves. The statement and its statement dependencies are unchanged.
- `citations.json`: one verbatim statement quotation for each node cited in each proof step.
- `searches.jsonl`: results logged by the required msearch.py command. All results were read. The item's earlier Q136 searches remain intact, and the present searches are appended to its search history.
- `report.md`: this report.

## Attachments

No attachment is requested. The dispatcher's earlier attachment rejection is binding for this attempt: I have delivered a split instead. In the current readable clone, `LinearMap.trace_eq_add_of_exact` is present at `lean/WeilConjectures/RingTheory/TateResidue/FinitePotent.lean:39`, with a proof through line 66. I read its hypotheses, conclusion and proof. They agree with the item, but I make no claim about its compiled transitive axiom closure. Its existing candidate metadata is preserved. No Lean file was written or compiled.

## WANTED

None. The necessary sources are present.

## Corrections and findings

The item was an unsplit, correct statement, with no argument. Tate's paper states finite-potent trace additivity for an invariant subspace, and its finite-dimensional case gives this statement after identifying the subspace and quotient. It does not supply the ordinary linear-algebra proof. I supplied that proof and marked `proof_origin.by` as `agent`.

The current Lean source differs from the state reported by the previous rejected attachment: the named file and theorem now exist. The brief explicitly forbids a second ATTACH answer, so this is disclosed rather than used to stop the task.

The search did not find a Mathlib declaration for the entire exact-sequence assertion. Direct-sum trace formulas assume that all summands are invariant; that cannot be imposed on a general equivariant exact sequence. The actual proof uses an arbitrary linear section, not an invariant complement.

The inherited brief points to `coord/dag-sync.md`, which is absent in this read clone. This does not affect the task: the current user brief supplies the live-clone and direct-delivery rules. No substitute synchronization or write to the repository was attempted.

## Unfinished work

None in the stage-1 split. Lower nodes already exist as Mathlib leaves. Stage 2, Lean writing and all compilation remain outside this task.

## Not duplicates

No new nodes were created. I initially considered a linear-section leaf, then found `lem-weil-pbc-vector-space-projective` and the lifting clause of `def-weil-pbc-projective-module`; together they supply it immediately, so it was folded into step 1. `lem-pc-finite-dimensional-trace-cyclic` already states the cyclic trace identity and was reused without modification. Neither the exact-sequence identity nor a clause of it was moved to a new node.

Whole-DAG searches covered trace cyclicity, linear left/right inverses, surjective linear maps, projective lifting, the Mathlib declaration names and Tag 09FN. Whole-blueprint searches used `tools/blueprint_refs.py search` for trace, trace with exact, cyclicity, right inverse, left inverse, surjective linear map, projective module, and 09FN. No blueprint node stating this exact item was found. `ancestor` returned `sk-thm-picard-duality`, agreeing with the preserved provenance chain. The current blueprint unit was read at `literature/blueprint/main-20261015/blueprint/sec-picard-framework/sk-thm-picard-duality/_section.md`: this lemma serves its Tate-residue trace input below the unit. The unit and chapter records were read and left untouched.

## Review by Q16

I read Tate, *Residues of differentials on curves*, the local PDF, Section 1, printed pages 149–151. Its (T1) identifies finite-dimensional Tate trace with ordinary trace; (T2) is invariant-subspace/quotient additivity; (T5) supplies the cyclic trace context. This delivery isolates the finite-dimensional argument and does not appeal to Tate additivity itself to prove it. I also read Stacks `fields.tex`, Tag 09FN (`lemma-vector-space-is-free`), and the following splitting discussion, and `algebra.tex`, the projectivity definition Tag 05CE and characterization Tag 05CF (`lemma-characterize-projective`). The new proof follows those lifting notions and the matrix definition of trace.

For step 1 I opened both cited nodes. `lem-weil-pbc-vector-space-projective` says every vector space over a field is projective, with no finite-dimensional or algebraic-closure requirement. `def-weil-pbc-projective-module` explicitly states that every linear map from a projective module lifts along every surjection. Thus applying it to the identity of C and the given surjective q really gives a linear s with qs=1. The step cites both assertions; it does not infer lifting from a bare name or from a proof hidden inside a node. I read the supporting Mathlib declarations: `Module.Free.of_divisionRing` at `LinearAlgebra/Basis/VectorSpace.lean:156`, `Module.Projective.of_free` at `Algebra/Module/Projective.lean:161`, and `LinearMap.exists_rightInverse_of_surjective` there at line 111. The range/top version of surjectivity was checked in `Algebra/Module/Submodule/Range.lean:90`.

For step 2, every inference is written out: q(b-sq(b))=0, exactness supplies the preimage under i, and injectivity gives uniqueness and the two linearity identities. Evaluating on i(a) proves ri=1; evaluating on b gives ir+sq=1. There is no unnamed complement theorem, quotient identification, invariant-section hypothesis or new subclaim with different hypotheses. It is an elementary construction from the actual assumptions.

For step 3 I opened `def-weil-endomorphism-trace`. It defines trace as the sum of diagonal coefficients in a finite basis. This is exactly what the step uses: the same-basis coefficient identity for a sum proves trace additivity directly. No unsupported trace-linearity theorem is hidden behind a definition citation. All three original spaces are finite-dimensional, so every ordinary trace in the proof is defined. The distribution of f_B over ir+sq is a pointwise identity of linear maps.

For step 4 I opened `lem-pc-finite-dimensional-trace-cyclic`. Its statement is precisely tr(ba on A)=tr(ab on B) for linear maps between two finite-dimensional spaces. Taking its two spaces to be (B,A) with maps (r,f_B i), and then (B,C) with maps (q,f_B s), gives exactly the two displayed replacements. I read the Mathlib match `LinearMap.trace_comp_comm'` at `LinearAlgebra/Trace.lean:265–269`, including the surrounding finite/free hypotheses. The cited node is a Mathlib leaf and does not depend on this item.

Step 5 is direct substitution using the two original commutation hypotheses, ri=1 and qs=1. It requires no additional result. I checked every citation against its statement and copied the full statement verbatim into citations.json. The only citations outside this unit are existing Mathlib leaves or definitions, so they are tools under the route rule; no off-route unresolved theorem is used.

I checked small cases: the zero exact sequence gives 0=0+0; A=0 or C=0 reduces to trace under the resulting linear isomorphism, which the same cyclicity calculation proves; and B=k^2, A=k e_1, C=k with f_B=[[a,u],[0,c]] allows arbitrary u and yields a+c. In particular the nilpotent Jordan example a=c=0,u=1 has no invariant complement, and the proof still works. Nothing requires characteristic zero or division by a dimension. Dropping compatibility would be false (take i=1 on k, C=0, f_B=1 and f_A=0), so both intertwining assumptions were retained exactly.

I reviewed the B–E return checklist against the files: no new unsplit-node proofs, no added notions, no duplicate nodes, no restatement split, no circular dependency, no source-only citation in place of an argument, no extra field hypothesis, and no weakened conclusion. All five proof steps are shorter than 2000 characters; their constructions and calculations are explicit. All search records added by this attempt are queries actually logged by msearch.py. One initial grep targeted a single file and its output omitted filenames; the resulting malformed entries were disclosed and repeated using directory searches before drawing a conclusion.
