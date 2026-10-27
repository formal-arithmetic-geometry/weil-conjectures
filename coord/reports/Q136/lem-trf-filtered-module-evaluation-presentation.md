# Q136 stage-1 delivery

## Files written

- dag/nodes/sec-trace-formula/lem-trf-filtered-module-evaluation-presentation.json: statement, split into six elementary finite-sum calculations; no exact Mathlib match.
- citations.json: one verbatim statement quotation for each node used by each numbered step.
- report.md and searches.jsonl: review and the actual recorded searches.

There are **0 new nodes and 0 new Mathlib leaves**. The four existing definition nodes used below are Mathlib leaves. No Lean source was written, no compiler or Lake command run, and no repository or launcher file changed. The sandbox initially had only dispatcher marker files, with no earlier split, report or search log to recover. No repair note exists for this item.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint tag, filtered presentation, filtered-module evaluation, filtration and dehomogenization terminology. Read RingTheory/Dehomogenization.lean (polynomial homogeneous-localization algebra equivalence) and Algebra/FiniteReesModuleGeneration.lean (eventual single-degree generation). Neither states this increasing filtered module evaluation kernel or the arbitrary evaluated presentation. The item's live node has no attached Lean declaration or lean_audit. No sorry declaration is treated as a finished proof.

## Wanted sources

None. Read literature/stacks-project/more-algebra.tex, Tag 053E, label lemma-flat-finite-type-valuation-ring-finite-presentation, statement and proof of (2), and algebra.tex, Tag 052N, label lemma-homogenize, statement and proof through its “Some details omitted.” These explain the finite graded module/dehomogenization route; the finite-sum expansion supplied here is agent-written, as proof_origin records. It does not claim that Stacks states the full stronger arbitrary-presentation formulation verbatim.

## Findings and changes

The statement is true as written and is unchanged. The initial node had no proof. It needs no valuation-ring, flatness, finite-generation, or degree-one-generation hypothesis to identify its evaluation quotient. Those are hypotheses of the parent use of 053E, not this elementary algebra assertion. Added the existing direct-sum and quotient-module definition nodes to stmt_deps because the statement uses these constructions. The increasing filtration is explicitly a family of submodules, so it is defined inline rather than through Mathlib's different decreasing ideal-filtration notion.

Read the chapter record sec-trace-formula and unit sk-i-curve-zero, then the latest blueprint normal-cone/contracting-correspondence proof lem-trf-local-term-locality.proof.md and the unit _section.md, under literature/blueprint/latest (snapshot main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345). This is a supporting algebra calculation in the inherited valuation finite-presentation branch, not a change in the chapter or unit route. The current item's blueprint.from already precisely identifies Steps 5 and 6 of its parent. Kept that place and ancestry. No source prohibited by the route lock is used.

DAG searches included 053E, 052N, dehomogenization, X_0-1, increasing filtration, filtered module, and right exactness; blueprint_refs searches for “dehomogen”, “filtered module”, and “homogeniz” returned no blueprint matches. Read the existing finite-graded-module-dehomogenization statement: it proves finite generation of homogeneous localization under different hypotheses, not this quotient and evaluated-presentation assertion. The existing module-pushout-quotient-presentation node concerns a binary module pushout. No duplicate node is introduced.

Mathlib searches were run only through msearch.py, with their exact query text and real results recorded in searches.jsonl and appended to the item's historical mathlib_searches. Two semantic phrasings were read. IsModuleFiltration is a definition, Ideal.Filtration concerns decreasing ideal-compatible submodules, and DirectSum.ker_lmap concerns componentwise direct-sum maps rather than the summation map. Module.FinitePresentation base change treats the tensor product but does not identify this filtered module with that tensor product in a one-line specialization. Polynomial homogenization results concern polynomial evaluation, not the entire module assertion. Loogle returned no hits; all services used in this run answered successfully.

## Review by Q136

I reviewed the source statements and proofs at 053E and 052N against the unchanged item. Stacks 053E(2) reduces a finite flat module over a valuation ring to a finite graded polynomial module; 052N constructs homogenized relations and leaves the module verification implicit. This item isolates the evaluation verification, and I have supplied it by explicit operations on finite-support families. No new statement-only nodes or sources need review.

Step 1 uses def-weil-pbc-direct-sum-modules, whose statement explicitly gives finite-support families, componentwise operations and finite decomposition into summands, and def-weil-pbc-mv-polynomial-ring, whose statement explicitly gives monomial multiplication, finite sums and evaluation. I checked that the increasing filtration makes S_0 land in the next summand, T_i(F_d) is in F_(d+1), and commuting T_i makes the displayed S_i commute. The polynomial action is constructed by a finite formula; no universal property for a commutative endomorphism ring is incorrectly assumed (the full endomorphism ring need not be commutative).

Step 2 uses exactly those same two definitions for the finite sum and evaluation. The generator equations epsilon(S_0 z)=epsilon(z) and epsilon(S_i z)=T_i epsilon(z) extend to each finite monomial and sum, proving all-variable P-linearity rather than just A-linearity. Exhaustiveness alone supplies the single-component lift of each m. Nothing assumes F_0=M.

Step 3 cites the direct-sum definition only. Its content is the displayed calculation y_d=-sum_(i<=d) x_i for d<D; increasingness puts every y_d in F_d. Checking degrees 0, intermediate degrees and D gives (X_0-1)y=z with the stated sign. The reverse inclusion follows from Step 2. I checked D=0 separately (the zero vector) and D=1 explicitly: y_0=-x_0=x_1 and (X_0-1)y has components x_0,x_1. This is an elementary finite-sum calculation rather than an appeal to an unproved Rees-module theorem.

Step 4 cites the polynomial and quotient-module definitions. The former states finite monomial expansions and their multiplication; regrouping by the exponent of X_0 is a finite regrouping. The geometric-sum identity p-s(rho(p))=(X_0-1)sum_(k>=1) s(q_k)(1+...+X_0^(k-1)) proves the polynomial kernel directly. The quotient definition states the coset operations, quotient surjectivity and kernel. Together with Steps 2 and 3, it proves that [z] maps bijectively to epsilon(z); the inverse coset is independent of the lift. I explicitly verified the Q-scalar formula. No first-isomorphism theorem, tensor-quotient theorem, or module-localization comparison is used without citation.

Step 5 uses the polynomial definition for entrywise substitution, multiplication and finite summation. The two displayed identities compare the actual augmentation and actual matrix entries on arbitrary vectors, so the proof is not just existence of an abstract presentation. Surjectivity uses only the already-proved evaluation surjectivity and the given surjectivity of pi; the composite with H(1,X) vanishes by the given pi H=0.

Step 6 again uses polynomial evaluation and the existing def-sc-finitely-presented-module, whose statement is exactly existence of an exact sequence of two finite free modules followed by M and 0. For a kernel vector a, the correction w-(X_0-1)c lies in ker pi because pi(c)=y. Given exactness of the original presentation yields b with Hb=w-(X_0-1)c; evaluation kills the correction and gives a=H(1,X)rho(b). No flatness of P/(X_0-1) is assumed; no tensor right-exactness is cited implicitly. The final finite-presentation assertion is literally the cited definition applied to this exact sequence.

I checked delivery-errors B–E against the open files. Each dependency quote is copied from its statement, not its proof. Every uses entry is in proof_deps and every statement notion added has its defining node. There are no new nodes that might be elementary, duplicate, or restatements; elementary algebra is kept as proof steps with the full calculation. All six steps are below 800 characters, so none hides a lemma in a long step. The hypotheses used are only commutativity of A, commutation and A-linearity of T_i, increasingness, exhaustiveness, and the supplied exact presentation. Each is used at the places identified above. The statement and maintainer-owned fields were retained, and blueprint.same_as is [] after search.

Additional small cases: n=0 reduces to the shift on an arbitrary exhaustive filtration and Q=A; M=0 works with arbitrary relations; A the zero ring gives only the zero module; v=0 forces N=M=0 and the evaluated sequence is exact; u=0 gives a zero kernel by the same correction argument. Constant filtrations F_d=M and delayed filtrations F_d=0 for d<r, F_d=M for d>=r verify that no assumption about the first nonzero degree is hidden. As a nonconstant example, take A=Z, M=Z[1/2], F_d=2^(-d)Z, T_1(x)=x/2. Then N=Z[X_0,X_1]/(2X_1-X_0), and evaluation gives M=Z[X_1]/(2X_1-1), exactly the claimed evaluated matrix relation. No cancellation in A, M, or X_0-1 is required anywhere.

Corrections made while writing: supplied the commuting endomorphism action explicitly, separated the D=0 case, checked the sign in the partial-sum kernel preimage, and replaced an abstract appeal to tensor right exactness by the concrete correction vector. This removes the need for a helper node that would merely restate a clause of the item.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs.

## Unfinished work

No mathematical step remains open. Required server dry run and direct push follow this review.
