# Q59 stage-1 report: lem-sfb-serre-graded-triangular-quotient

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-serre-graded-triangular-quotient.json`: item, statement unchanged, split into seven complete steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-weyl-relations-free-normal-form.json`: new statement, unsplit, no Mathlib match after two semantic phrasings, LeanSearch, Loogle and recorded source searches. It concerns the different, Weyl-only algebra before any Serre relations are imposed.
- `dag/nodes/sec-six-functors-basics/lem-sfb-free-lie-homogeneous-presentation-grading.json`: new statement, unsplit, no Mathlib match after two semantic phrasings, LeanSearch, Loogle and recorded source searches. It is a general free-Lie grading and homogeneous-relation-ideal theorem, with no Cartan or triangular-decomposition content.
- `citations.json`: all 13 step/node incidences, each with a literal part of that node's statement. For the two new nodes the quote is the full statement, displaying both the hypotheses and the precise normal-form, grading, quotient or ideal-span clause used. Lie-definition citations quote Jacobi/alternation or the ideal/quotient definitions as appropriate.
- `searches.jsonl`: the actual search-command log; all current searches were read, and the imported item's earlier searches were retained. No Lean file was written and no compiler was run.

There are two new nodes and zero Mathlib leaves. The local helper `write_split.py` only constructs these sandbox JSON files and is not a project delivery file.

## Attachments

None. Searches for the exact blueprint tag, Serre, Chevalley, triangular decomposition, free Lie, homogeneous Lie and Weyl relations under the live `lean/WeilConjectures/` found no declaration stating the item. Related Lie files concern solvability and existing representations. The same searches under `lean/Sheaf/` found no replacement proof. Mathlib's `Matrix.ToLieAlgebra` is a definition, not a proof of this item.

## Sources and WANTED

I read Milne, *Algebraic Groups* (2017), printed pp.503–505 (PDF pages 515–517) and p.508 (PDF page 520). The first proof of Theorem 23.63 is the route: first form the Weyl-only algebra with free positive and negative factors, then impose the two Serre families. Milne refers the first theorem to Bourbaki and the second passage to Serre instead of proving the details. I have not claimed the generic grading statement or arbitrary-matrix generality is proved by Milne. The item's proof is consequently marked `proof_origin.by = agent`. Stacks does not supply these Lie-theoretic inputs; no unrelated Stacks tag or prohibited SGA source is substituted.

WANTED: Bourbaki, *Lie Groups and Lie Algebras*, Chapter VIII, §4, no.2, the direct proof of the Weyl-only free normal form referred to by Milne p.504, for lem-sfb-weyl-relations-free-normal-form.

WANTED: Serre, *Complex Semisimple Lie Algebras*, Chapter VI and its appendix, the Serre-presentation argument referred to by Milne p.504, for lem-sfb-serre-graded-triangular-quotient and its two supporting nodes.

WANTED: a detailed account of free Lie algebra multigradings and homogeneous relation ideals, such as the free-Lie-algebra treatment in Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, for lem-sfb-free-lie-homogeneous-presentation-grading. No precise subsection not read locally is asserted.

For the normal-form node, the expected subsequent proof is the usual bracket-word spanning argument and universal lowest/highest-weight word representations. For example, on the tensor words in letters f_j, with a freely chosen tuple lambda, put F_j(w)=f_j w, H_i(w)=(lambda_i-sum_j m_j b_ij)w for a word of content m, E_i(1)=0, and recursively E_i(f_j w)=f_j E_i(w)+delta_ij H_i(w). Induction verifies exactly the four Weyl relations. Varying lambda detects every nonzero Cartan linear combination, and opposite word representations detect the two free factors. Proving the free-Lie-to-word-algebra injection is part of this still-unsplit input; it is not silently taken from the finite-dimensional node lem-sfb-rational-pbw. There are no finite-type or invertibility conditions in this construction. This paragraph is a plan for the new node, not a claim that stage 1 has already split it.

For the grading node, a subsequent proof can start from the vector space on nonempty fully bracketed words. Degree is the sum of letter degrees. The alternating, skew and Jacobi relations have homogeneous generating versions (over Q, polarizing alternation handles inhomogeneous inputs); closure under bracketing and linear combinations preserves the degree decomposition of their relation ideal. The same closure argument for specified homogeneous s_t produces exactly the iterated-adjoint spanning formula in the statement. This free-presentation argument, including independence of components rather than just existence of a degree assignment, is why the node is a real supporting theorem. It is not merely a definition of grading.

## Corrections and dependency audit

The item was unsplit with no proof and no repair order. Its full statement is correct and retained, including arbitrary generalized Cartan matrices, singular matrices, all three summands, simple-degree nonvanishing, higher multiples vanishing, and the empty-index case. No STATEMENT-DISPUTED correction was needed. The inherited source already warns about Milne p.504's typographical errors: [X_i,X_i]=H_i must read [X_i,Y_i]=H_i, the H/F relation has the negative sign, and the printed J_j in the negative Serre relation means Y_j. I used the corrected relations already present in the item's statement.

There were no imported proof dependencies to remove. The only statement dependency remains def-wf-lie-algebra; free algebras and gradings are explicitly explained in each statement. The item now cites the two new supporting theorems and the existing Lie definition. The new theorems have empty proofs and empty proof dependencies and cannot cycle back to the item.

I read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-images proof. This is an inherited, deeply nested representation-theoretic prerequisite of the direct-image route, not a new replacement of its sheaf-theoretic steps. Neither the unit record nor chapter is changed. `tools/blueprint_refs.py ancestor` reports no blueprint ancestor (None) along this inherited chain, matching the item's existing `from.node = null`; new nodes retain that value and prepend the item to its exact via chain. Each new `from.place` identifies the supporting argument in the inherited chain. Searches across the entire imported blueprint for free Lie, Weyl relations, graded Lie, homogeneous Lie, homogeneous relations, Serre relations and triangular decomposition found no statement covering either input; searches of the newest blueprint text likewise yielded no Lie-presentation theorem. `same_as` is therefore empty on all three nodes.

## Not duplicates

- lem-sfb-weyl-relations-free-normal-form vs lem-sfb-serre-graded-triangular-quotient: W(B) has only Weyl relations, has free Lie positive/negative factors, and allows any rational matrix. The item concerns its further quotient by both Serre ideals. The item's main calculation establishes that these are ideals of W before quotienting, not an application of the item's conclusion under a new name.
- lem-sfb-weyl-relations-free-normal-form vs lem-sfb-serre-rational-presentation: the latter assumes a finite reduced root system and proves finite-dimensional semisimplicity and the prescribed root datum after Serre quotienting; it is an ancestor, not an available proof of the Weyl-only theorem.
- lem-sfb-weyl-relations-free-normal-form vs lem-sfb-rational-pbw: that PBW statement assumes an already given finite-dimensional rational Lie algebra. W(B) generally has infinite-dimensional free factors, and the PBW statement supplies no decomposition or injectivity for this presentation.
- lem-sfb-weyl-relations-free-normal-form vs lem-sfb-verma-monomial-weight-basis: the latter assumes an already realized finite-dimensional split semisimple algebra and a root decomposition, which the Weyl-only theorem neither assumes nor concludes.
- lem-sfb-free-lie-homogeneous-presentation-grading vs lem-sfb-serre-graded-triangular-quotient: the generic statement has arbitrary generators, abelian grading group and homogeneous relations, but no normal form, Cartan independence, sign-cone support or Serre quotient identification.
- lem-sfb-free-lie-homogeneous-presentation-grading vs lem-sfb-gm-representation-weight-basis: a torus-representation weight decomposition is not a construction of a free Lie presentation's grading and its homogeneous ideal components.
- lem-sfb-free-lie-homogeneous-presentation-grading vs lem-sfb-homogeneous-ideal-radical: the latter concerns ideals of a commutative polynomial ring and their radicals, not free Lie algebras and Lie relation ideals.

No Stacks tag is shared by a new node with an existing node. The all-DAG keyword search found no existing free-Lie homogeneous-presentation or Weyl-only normal-form statement.

## Mathlib reading

All recorded queries were run with the required msearch.py command; the 16 actual output records are in searches.jsonl. I read `Algebra/Lie/SerreConstruction.lean:13–56,94–147`: it defines the correct presentation but contains none of the asserted structure theorems. In particular, the search hit `CartanMatrix.Generators.H.inj` refers to the constructor of the generator type before taking the quotient; it proves neither nonzero H_i nor their linear independence in the presented Lie algebra.

I read `LinearAlgebra/RootSystem/GeckConstruction/Basic.lean:160–200`: it constructs a matrix subalgebra of a given finite root pairing and its distinguished Cartan subalgebra. It does not identify a universal generalized-Cartan presentation. I read `Algebra/Lie/Basis/Basic.lean:13–75`: its structure assumes both Cartan linear independence and a nondegenerate matrix, so it cannot establish either in W or handle the item's singular cases.

For the grading node I read `Algebra/Lie/Free.lean:75–132`, `Algebra/Lie/Graded.lean:12–95`, the direct-sum Lie setup, and `LinearAlgebra/TensorAlgebra/Grading.lean:12–65`. The first constructs the free object without its grading, the second assumes a grading and gives its decomposition, and the tensor-algebra result gives an associative total-degree grading. DirectSum.lieAlgebra has componentwise brackets, not mixed brackets in degree gamma+delta. None specializes in one line to the new statement. No candidate is promoted to a Mathlib leaf.

## Review by Q59

I checked delivery-errors B–E with the node statements and sources open. The new nodes are self-contained statement-only theorems, their objects and universal properties are introduced, their source limitations are explicit, and all of their recorded searches actually ran. They have the item's chapter/unit, the inherited blueprint chain and exact supporting places. I ruled out elementary nodes and re-labelled conclusions: neither new theorem states a clause about L(A); the grading lemma supplies the nontrivial independence of homogeneous pieces, and the normal-form lemma supplies structure of the larger W(B), while steps 3–6 carry the Serre argument itself.

Step 1 takes the canonical vector-space isomorphism and injectivity from the precise statement of lem-sfb-weyl-relations-free-normal-form, which I reread in full. Its hypothesis is an arbitrary rational matrix on a finite set, so the item's integer matrix qualifies without an extra determinant or root-system hypothesis.

Step 2 uses the free-word grading, homogeneous generated-ideal assertion and quotient grading from the actual statement of lem-sfb-free-lie-homogeneous-presentation-grading; it uses the normal-form statement only to identify the two free positive/negative algebras inside W. I checked homogeneity of EF separately: delta_ij H_i contributes only when the degree of [E_i,F_j] is zero. In particular this argument does not mistake a Cartan-weight decomposition for the finer Z^I grading, which would be invalid for singular A.

Step 3 uses exactly the four relations displayed in the normal-form node and the Jacobi identity displayed in def-wf-lie-algebra. I checked both induction formulas, their r=0 initial values, the recurrence coefficient, and its vanishing at N=1-a_ij. The exceptional F_j bracket reduces to -D^N H_j. If N=1 it really requires a_ij=0 implies a_ji=0; if N>=2 it vanishes by [E_i,E_i]=0. Thus no unmentioned sl2 representation theorem or finite-dimensionality is being used.

Step 4 uses the same explicitly displayed relations and Jacobi/ideal definitions. Its two inductions have a defined span V, a base (the Serre generators), and an explicit step. In the F_k computation, -delta_kl[H_k,u] belongs to V by Cartan stability already proved, so the proof does not assume the conclusion it is establishing. The final generator-to-W bracket induction is justified by W's actual presentation. This step does not cite a definition as a black box for ideal stability: it proves that stability.

Step 5 checks the actual Weyl presentation under E/F exchange and H negation. Its inverse is the same assignment, verified on generators by the free universal property. This supplies the negative case without assuming an unproved opposition theorem. The equality J=K^++K^- uses both minimal-ideal containments; directness comes from the normal-form isomorphism. Step 6 uses that same isomorphism and the literal ideal/quotient definitions in def-wf-lie-algebra. Its kernel calculation is written out, so there is no unsupported assertion that the two quotients commute or that a vector-space decomposition is a direct product of Lie algebras.

Step 7 uses the grading lemma's bracket-word and generated-ideal statements and the alternation in def-wf-lie-algebra. I checked that Serre generators have height at least two and adjoint words in the positive algebra only add nonnegative height. Thus they cannot kill degree epsilon_i. A free map to the one-dimensional abelian algebra detects E_i before the quotient. A bracket word with degree n epsilon_i uses only E_i, and its length induction is explicitly given, not an appeal to classification of finite root systems.

Small cases checked: the empty set gives zero; a singleton gives the three-dimensional sl2 presentation for A=(2), with no Serre generators and no higher one-letter brackets. For the normal-form input alone B=(0) gives the three-dimensional Heisenberg presentation, illustrating why b_ii=2 is not needed there. The disconnected two-vertex matrix diag(2,2) has N=1 and both opposite off-diagonal entries zero, so both Serre ideals are stable. For a_ij=-1, N=2 and the coefficient -2(a_ij+1) vanishes as required. The singular affine matrix [[2,-2],[-2,2]] still has an independent two-dimensional Cartan space, including its central direction; the proof never inverts A. As a check of the necessity of the hypotheses rather than a counterexample to the item, if a_12=0 but a_21=-1 then [F_2,[E_1,E_2]]=a_21 E_1 is nonzero in W, precisely where the symmetric-zero hypothesis prevents failure.

I also checked degree-zero/negative-degree assignments, zero relations, and empty generator/relation sets in the generic grading statement. Their allowance is needed because the H generators have degree zero. Every item step is below 2000 characters (maximum 1489); none hides a long unrecorded comparison theorem. The seven routine arguments beyond the two cited non-elementary inputs are fully written, not delegated to new nodes for individual clauses.

## Completion and checks

The one-level stage-1 split is complete; the two new statement-only inputs intentionally remain for later workers. No claim is made to have written or compiled a Lean proof. The server-side review_split invocation passed. The required full delivery dry run and push are performed after this report is written; their output is the delivery evidence.
