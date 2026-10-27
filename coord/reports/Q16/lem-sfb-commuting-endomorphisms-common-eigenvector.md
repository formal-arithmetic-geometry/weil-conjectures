## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-commuting-endomorphisms-common-eigenvector.json — item, statement, split; no direct Mathlib match, with all five searches run in this sandbox recorded alongside the inherited searches.
- citations.json — verbatim statements for both citations in proof step 2.

No new nodes and no new Mathlib leaves. The two existing Mathlib leaves reused are lem-zl-alg-closed-endomorphism-eigenvalue and lem-trf-vector-space-quotient-dimension.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for common eigenvectors, common eigenlines, eigenvalues and commuting operators. The project declaration LieModule.exists_ne_zero_forall_lie_eq_smul_of_isSolvable requires characteristic zero and a Lie-module structure. It does not state this arbitrary-characteristic finite-family assertion.

## Wanted literature

None. Read Milne, Algebraic Groups, Lemma 16.11 and its proof on printed p.327 (PDF p.339). The source is available as literature/milne-algebraic-groups_iAG2017.pdf.

## Findings and changes

The statement is correct and has been retained verbatim. The item was statement-only, and its seven inherited searches already explained why generalized joint eigenspaces do not immediately prove the true common-eigenvector assertion. There was no earlier sandbox item, report or search log to continue. Those inherited search records were retained; the five searches run here are additional, actual logged searches.

Milne proves the stronger arbitrary-set triangularization theorem by dimension induction, first producing a one-dimensional stable subspace. For the present finite-family assertion, the proof uses the same invariant-eigenspace construction but inducts on the number of operators. This avoids the unnecessary proper-eigenspace/scalar-operator case distinction. The proof is marked agent-written because of this explicit change of induction parameter. It remains the same linear-algebra input to the existing route below the unit; neither a unit statement nor its route is changed. Read the chapter record, the unit record, and the current latest blueprint sk-thm-sf-ctf-stability text. The item is a supporting created node, not the unit's key statement, so no unit realization fields were changed.

Blueprint searches for eigenvector, eigenvalue, commuting, and common eigenvector found no equivalent imported statement. lem-wf-solvable-common-eigenvector is over the characteristic-zero coefficient field, not an arbitrary algebraically closed field. The ancestor command reports None for this existing created-node ancestry; the existing null blueprint.from.node and detailed from.place/via are retained, and same_as remains []. No new provenance chain was invented.

## Unfinished work

None in the stage-1 split. No Lean was written and no compiler or build was run. Validation and delivery use the required server-side dry run and delivery tool.

## Not duplicates

No new nodes were created. The DAG already contains the exact single-operator eigenvalue theorem as lem-zl-alg-closed-endomorphism-eigenvalue, and subspace finite-dimensionality as a clause of lem-trf-vector-space-quotient-dimension. Both are reused rather than duplicated. The eigenvalue node is strictly a one-operator input, not a restatement of the finite-family item.

## Review by Q16

I read Milne's Lemma 16.11 and the proof on printed p.327, including the identity that makes an eigenspace invariant under commuting operators. I read the complete statements of both cited DAG nodes and the Mathlib source for Module.End.exists_eigenvalue in Eigenspace/Triangularizable.lean:63–66, the submodule-finiteness instance in FiniteDimensional/Defs.lean:132–134, the joint generalized-eigenspace theorem in Eigenspace/Pi.lean:194–202, and the Lie weight-space candidates. The latter require extra Lie-algebra/weight-space constructions; the inner-product candidates require symmetry. None is an exact or one-line Mathlib match for this item.

Step 1 states the induction claim universally over the ambient vector space, so the hypothesis can later be applied to an eigenspace of a different space. Its empty-family case uses exactly the item's nonzero hypothesis; there are no scalars to choose in that case. Choosing an index and removing it decreases the finite cardinal by one, and no linear-algebra theorem is hidden in this step.

Step 2 uses lem-zl-alg-closed-endomorphism-eigenvalue precisely for the scalar a and nonzero vector z satisfying the eigen-equation. All its hypotheses hold: k is algebraically closed, V is finite-dimensional and nonzero, and the chosen operator is linear. It defines E by the equation, proves closure under linear combinations, and exhibits z as a nonzero element. The statement of lem-trf-vector-space-quotient-dimension explicitly says that every linear subspace U of a finite-dimensional V is finite-dimensional. This is exactly the clause used with U=E; no quotient dimension assertion is assumed to give something else. Full verbatim statements are in citations.json. Both cited nodes are Mathlib leaves and legitimate generic tools outside this unit; no route replacement occurs.

Step 3 derives stability by the displayed calculation T_i0(T_j x)=T_j(T_i0 x)=a T_j x. It checks commutativity of the restrictions by evaluating both composites on an element of E, then applies the already established smaller-index induction assertion. Injectivity of inclusion preserves nonzeroness, and defining lambda_i0=a and lambda_j=b_j proves each equation in V. Stability, restriction and assembly are explicit elementary calculations, not new lemmas or an appeal to an uncited simultaneous-triangularization theorem. The only non-elementary step is step 2, with its two existing cited inputs. Every step is below 2000 characters.

I checked the B–E return cases against these files: no statement-only child contains a proof because there are no new children; all objects and hypotheses are introduced; source locations are precise; no invented Stacks tag or forbidden SGA source occurs; no clause is moved into a renamed node; and each cited statement really supplies its use. The finite-index induction has an explicit base and step. The two leaves cannot create a dependency cycle back to this item. Small cases checked were the empty family, a singleton, dimension one, zero operators and zero eigenvalues, and all-scalar families. A two-by-two nilpotent Jordan block illustrates why the eigenvector statement requires no diagonalizability. No step uses characteristic zero, invertibility, distinct eigenvalues or positive eigenvalues. The excluded zero-dimensional V would fail the conclusion, so its exclusion is retained.
