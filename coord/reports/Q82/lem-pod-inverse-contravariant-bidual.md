# Stage-1 report: lem-pod-inverse-contravariant-bidual

## Files written

- dag/nodes/sec-poincare-duality/lem-pod-inverse-contravariant-bidual.json: statement, split into six proof steps; not a Mathlib leaf.
- citations.json: one exact statement quotation for every proof-step citation.
- report.md: this report. searches.jsonl records the executed searches; write_split.py is sandbox-only preparation code, not a delivery file.

New nodes: 0. New Mathlib leaves: 0. The item's statement and statement dependencies are unchanged. All prior source, creation, blueprint and search records are retained.

## Attachments

None. Searched the project under lean/WeilConjectures by the exact blueprint id and by bidual, contravariant and contragredient, then read the finite-coefficient DualTateData and WeilDual interfaces. Their finite-coefficient evaluation theorems do not state the rational completed/localized comparison and coefficient-bidual equation of this item. The generic map_toIhomIhom_comp_dualComparison in SixFunctors/Etale/Derived/DoubleDual.lean, lines 215–227, supplies a related abstract core but does not instantiate the required rational partial closed operations or the inverse-contravariant Weil equation; it is not an attachment of this item. No compiler was used.

## WANTED

None. The calculation is an agent-written expansion of the blueprint's evaluation/transposition argument using the existing cited interfaces, not a claimed new literature theorem.

## Findings and source checks

The historical source path in the item places prop-weil-operations in sk-lem-finite. In literature/blueprint/latest it has moved to sec-poincare-duality/sk-thm-frobenius. Read both its statement and proof there, and the paragraph beginning “The dual Weil structure” in latest/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md. The latter gives the inverse first-variable datum, evaluation naturality and transposition route. The proof sources and proof_origin refer to the current latest path. No SGA source is used. No statement dispute was found.

The item is a support lemma below the imported unit, not its key node; no chapter or unit record is changed. The calculation supplies the coefficient-bidual part of the retained rational pairing proof. It does not replace any unit-level finiteness step. Generic off-unit tools are declared in split_report.tool_uses.

## Mathlib and duplication searches

Read and reused searches.jsonl, including the interrupted second LeanFinder search, whose successful result was recorded before the pause. Ran all four requested services with a second semantic phrasing. The narrow grep and Loogle pattern returned no hits. LeanSearch returned ordinary module duals, the double order dual and a dual-existence transport lemma, none of which states this assertion. The second LeanFinder query returned compTranspose and expComparison/coev facts; a follow-up search-command grep located their files and lines. Read Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean lines 380–410 and Closed/Functor.lean lines 65–110: compTranspose is the definition of uncurried internal composition; expComparison there is in the Cartesian/product setting. Neither is the rational sheaf coefficient-bidual statement or a one-line specialization giving it. Thus no Mathlib attachment or leaf was asserted. The exact queries and observed hit summaries are appended to the existing item's mathlib_searches; no search is invented.

Searched the whole DAG and imported blueprint for bidual and evaluation (blueprint_refs.py), plus DAG keywords for site-perfect duals and rational tensor symmetry. The point-biduality blueprint theorem only concerns perfect point complexes and asserts invertibility, without inverse-contravariant Weil equivariance. Existing lem-sf-evaluation-bidual-comparison-transport is a generic transport interface, not this Weil assertion. Reused the already-existing dual-stability, rational transpose and comparison nodes instead of creating duplicates or a new node restating the item.

## Not duplicates

No new nodes. The two evaluation identities are elementary substitutions in existing statements and remain proof steps. The two uncurried-composite calculations remain proof steps, rather than being made into clause nodes.

## Review by Q82

I read the full statements of every cited node before using them. I checked the following applications against those statements and the current blueprint sources, rather than relying on their titles or on their proofs.

Step 1 uses lem-sf-perfect-dual-pair-and-tate-stability for its explicit “P-dual and its twist are perfect” assertion, specializing to E, zero twist and zero shift, and applying it again to the first dual. Its hypotheses allow a finite-type scheme in the coefficient datum; neither smoothness nor properness is assumed. Our separated finite-type X and site-perfect K are in this domain. I read its source anchor in latest/sk-thm-sf-dual-perfect/sk-thm-sf-dual-perfect.proof.md (perfect coefficient dual and coefficient biduality), but use only the generic node's statement, not that smooth theorem as a black box. The evaluation-comparison node supplies actual h for the two indicated Hom pairs, and says that the rational identities hold for arbitrary localized arrows. Internal Hom sends pairs of inverses to inverses by its bifunctor law, so beta and gamma are invertible without a stable lattice. This is not an invocation of an integral Frobenius structure.

Step 2 uses the naturality in all three variables and the evaluation formula of lem-coef-completed-tensor-hom-transpose. With the first-variable arrow u inverse, evaluating on u cancels that inverse. Its second-variable arrow is the actual coefficient datum c. The other cited node, lem-pod-derived-automorphism-hom-evaluation, states exactly ev(1 tensor h) mu = P(ev). Replacing mu by its inverse gives the two displayed pairing equations. The tensor/Hom orientation is argument-first throughout; the transpose tool explicitly retains signed symmetry, so the passage from its naturality to this argument order is justified.

Step 3 applies the rational bijection with first variable B=K-dual, target the coefficient unit, and parameter PA. The Hom pair (B,unit) is permitted by step 1 and by the h_B already specified in the item. The transpose tool's statement gives both the displayed evaluation formula and injectivity; it is not a mere full-faithfulness assertion. Precomposing with beta tensor identity is cancellable because beta is an isomorphism. The precomposition domain is PB tensor PA, not B tensor A.

Step 4 uses lem-coef-rational-tensor-symmetry-laws for naturality of the prescribed rational Koszul swap on the pair (beta,alpha); its E and separated finite-type hypotheses hold. It uses lem-pur-derived-pullback-tensor-iso for the exact signed-commutativity compatibility t_AB sigma = P(sigma) t_BA. The first evaluation equation was proved in step 2. Each arrow in this chain has source PB tensor PA and target the unit. The result is c P(b) t_BA.

Step 5 uses the second evaluation equation of step 2 and the same pullback-tensor tool's stated naturality, now with the pair (identity_B,j). Its field-stage naturality applies to arbitrary rational j, not only lattice-preserving arrows. Substituting the defining identity e_B(1 tensor j)=b gives exactly the same c P(b) t_BA as step 4. Thus this step does not silently assume that P commutes with the bidual map: it proves the needed equality using evaluation.

Step 6 cancels the specific tensor isomorphism, then uses the transpose bijection of step 3. I checked the full statement of def-weil-weil-sheaf-complex: its pair-arrow equation is precisely the resulting j alpha = gamma Pj. No assertion that an abstract isomorphism is the canonical bidual map is substituted. The delta retained throughout is the transpose of the specified signed evaluation.

For the B–E checklist: there are no new statement-only nodes to check for missing notions, proof leakage, false hypotheses or duplication. All non-elementary tools in the calculation are cited; citations.json was checked by literal substring against each cited statement. Proof dependencies are the union of step uses. Transitive dependencies of the candidate tools were checked for a path back to this item; none was found. All steps are under 2000 characters, and none hides a separate local-to-global or coefficient-descent argument. The proof stays entirely at E with arbitrary rational arrows. The zero object makes both evaluated composites zero; on a point with alpha=ell the dual data are ell inverse and ell, and the ordinary evaluation map commutes. On the one-shifted coefficient line the signed symmetry changes the usual bidual identification by its Koszul sign; both chains carry the same sigma and hence retain that sign. On degree-zero finite-dimensional vector spaces with any invertible matrix A, the data are inverse transpose of A and A after the canonical bidual identification, which checks the inverse convention. No step assumes positive rank, smoothness, properness, or a Frobenius-stable lattice.

## Unfinished work

No mathematical step remains in this split. New lower-level nodes: none. Required delivery checks and delivery result are recorded below after the tools finish.

## Validation

The first server dry run exited successfully: `OK (not pushed)` at 3b77632b44f, with preflight passed (including the required DAG and split checks). No local compiler or local gate was run. A final dry run follows this report update before delivery.
