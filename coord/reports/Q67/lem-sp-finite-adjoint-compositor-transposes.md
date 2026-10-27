# Stage-1 delivery: lem-sp-finite-adjoint-compositor-transposes

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-finite-adjoint-compositor-transposes.json`: statement, split into five proof steps; the statement and its statement dependencies are unchanged. Mathlib supplies the generic adjunction ingredients, already represented by existing leaves, but not the whole explicit coefficient-transpose calculation in one specialization.
- `citations.json`: the three step/node citations, each with a verbatim statement quote.
- `searches.jsonl`: actual search-command log, retained unmodified.
- `report.md`: this report.

There are zero new nodes and zero new Mathlib leaves. No repository or launcher file was written. No git command, Lean edit, compilation, Lake command, or subagent was used.

## Attachments

None. Searched the project Lean source for the exact blueprint tag and for compositor, rightAdjointUniq, and counit/transpose terminology. The generic declarations `CategoryTheory.Adjunction.rightAdjointUniq_ofNatIsoLeft_comp_counit` (ProjectionTensorMap.lean:269), `CategoryTheory.Adjunction.mateEquiv_inv_comp` (:379), `CategoryTheory.Adjunction.mateEquiv_inv_comp_rightAdjointUniq` (:499), and `CategoryTheory.Adjunction.existsUnique_iso_comp_counit` (Triangulated/BrownRepresentability/RightAdjoint.lean:160) supply related portions of the formal argument. They do not individually state all clauses of the item, including its explicit transpose of D. Consequently no attachment of the whole item is asserted.

## WANTED

None. The current blueprint, Stacks text, and pinned Mathlib sources needed here are present.

## What was wrong or incomplete

The item was a statement-only child of the repaired parent split. The source's exceptional coefficient paragraph says to use the two counit equations and naturality, but leaves their actual substitutions and the compositor factors implicit. This delivery writes them out. There is no statement dispute and no change to the unit or chapter route. The compact-support b composition identity is a hypothesis of this child; it is not proved again and the parent is not cited, avoiding a cycle. The finite transpose calculation neither invokes tower realization nor claims levelwise equality proves a derived tower equality.

The introductory full theorem, determinant/tensor theorems, and smooth-purity results are not imported as black boxes to prove this formal subclaim. All geometric adjunctions and scalar functors used here are the data expressly assumed in the statement.

## Unfinished work

None within this stage-1 item. The two existing Mathlib leaves used below already have their matches. No subordinate unsplit statements are introduced.

## Not duplicates

No new node is proposed, so there are no new/existing pairs to justify. Whole-DAG statement searches and `tools/blueprint_refs.py search` for adjunction, composite adjunction, counit-compatible, and coefficient comparisons found the generic existing nodes `def-weil-pbc-composite-adjunction`, `det-sp-unique-right-adjoint`, and `lem-cat-right-adjoint-composition`. The first two suffice and are reused. The parent `det-sp-composition-comparisons` contains the assembled geometric conclusion and already depends on this child; it is not a permissible dependency. The scalar-iterated-mate nodes concern ordinary etale pullback/direct-image adjunctions rather than these compact-support/exceptional adjunctions, so they are not silently substituted. The item's `same_as` remains empty because no distinct blueprint node states this child with its precise b-identity hypothesis and explicit intermediate transpose.

## Mathlib searches and sources read

Seven new queries were actually run by the prescribed msearch command, with their exact query texts and outputs recorded in searches.jsonl and appended to the item's existing search history. All services answered. The first Loogle conjunction returned no hits, so the second Loogle query directly tested mateEquiv_hcomp. LeanSearch found comp and its counit formulas; the second LeanFinder phrasing found horizontal/vertical pasting of mates. I read Basic.lean:555-589, Unique.lean:95-140, and Mates.lean:195-220. These establish that the needed general categorical facts already exist, and explain why no new generic node is created. The item requires several explicit substitutions and two compositor calculations in addition to these API facts, so it is delivered as a split rather than labeled a one-line Mathlib specialization.

The existing historical searches in the item were preserved. Their results are source material from the earlier parent split, not claimed as searches performed by Q67.

## Review by Q67

I read the current source `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.proof.md`, paragraphs (1) and (2), and its unit and chapter records. The argument follows their composition-of-adjunctions and counit-transposition route. I also read `literature/stacks-project/categories.tex`, Definition 0037 (`definition-adjoint`) and its following transpose formulas, and Lemma 0DV0 (`lemma-compose-counits`), plus the current categorical unique-adjoint blueprint proof. No SGA source is used.

Step 1 cites `def-weil-pbc-composite-adjunction`: its statement really supplies the composite Hom bijection and the counit epsilon_g after F_g epsilon_f. I checked the transported Hom map explicitly: u from L_R M to K is precomposed with alpha_R(M) inverse, hence the transported counit is epsilon_gf after alpha_R, in precisely that order. The other citation, `det-sp-unique-right-adjoint`, states existence, naturality, invertibility, and uniqueness of the counit-compatible comparison between two right adjoints to the same left functor. Its hypotheses apply after the transport, and it gives exactly the direction H_gf to H_f H_g. These two entire relevant statements were read, not their proofs used as additional hypotheses.

Step 2 applies naturality of the given f counit at c_g(K), whose domain is S_Y H_g,A K and whose target is H_g,B S_Z K. The remaining substitution is exactly the f coefficient-counit equation assumed in the item's statement, evaluated at U=H_g,A K. This is an elementary displayed calculation, with no uncited geometric theorem.

Step 3 substitutes the assumed g counit equation at K and writes naturality of b_g at a=epsilon_f,A(U): F_f,A N to U. I checked both sides run from F_g,B S_Y F_f,A N to S_Z F_g,A U. The inverse of beta_N is b_g(F_f,A N) inverse after F_g,B(b_f(N) inverse), so the result is exactly S_Z(E_A(K)) after beta_N inverse, not its reversed product. This proves the requested intermediate transpose and does not merely cite a renamed clause.

Step 4 checks that v=theta_A(K) has source H_gf,A K and target N; naturality of beta applies at precisely this map. The displayed four-line equality retains S_Z(alpha_A(H)) and then uses the hypothesis b_gf(H) S_Z(alpha_A(H)) = alpha_B(S_X H) beta_H. Multiplication by the two inverses gives the claimed last line. This calculation is necessary: omitting either alpha would compare morphisms with different left-adjoint normalizations.

Step 5 computes the other side's transpose. Naturality of alpha_B is used at c_gf(K), so alpha_B evaluated at H_gf,B S_Z K moves across L_B(c_gf(K)) in the displayed direction. The assumed gf counit equation then gives the identical result. The cited composite-adjunction statement explicitly says its Hom correspondence is a bijection, so equality of these transposes proves equality of the actual B-linear derived morphisms. I checked its statement again for this use; citations.json has the corresponding verbatim quote.

Every object in the calculation is in a category or the image of a functor supplied in the item's hypotheses; there is no application of a theorem requiring a larger field, a special coefficient quotient, or an unproved smoothness/permanence result. Functoriality, counit naturality, inverses of isomorphisms, and injectivity of the given Hom bijections are the only elementary operations in steps 2–5. Step 1 is marked non-elementary and names its two existing leaves. No step exceeds 2000 characters or hides an additional comparison lemma.

For small cases I checked f or g an identity (and relative dimension zero): the equations reduce to the original single counit equation. With A=B and identity scalar comparison the transpose is E_A itself; after the normalized compositors the final equation is the counit normalization of theta. The zero object and empty schemes yield the unique zero morphisms. The nonflat quotient Z/ell^2 to Z/ell uses the very same categorical formulas; no exactness of ordinary tensor, finite free resolution, or bounded projective dimension is used anywhere. These checks reveal no missing hypothesis or statement correction.

I checked delivery-errors B–E against the actual files: no new statement-only-node or duplicate issues arise; TeX is encoded once; every non-elementary external ingredient is cited; the proof is an argument rather than relabeling into new clauses; no parent dependency or cycle is introduced; the source and target of every inverse and compositor were checked. The union of step citations equals proof_deps, every citation quote is verbatim, the statement is byte-for-byte unchanged, and only worker-owned fields changed.
