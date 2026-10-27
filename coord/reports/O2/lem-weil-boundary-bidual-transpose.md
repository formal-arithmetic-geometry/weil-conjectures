# Worker report: lem-weil-boundary-bidual-transpose

## Files written

- `dag/nodes/sec-six-functors/lem-weil-boundary-bidual-transpose.json`: the existing statement, statement dependencies, source, provenance and inherited searches are preserved. Eight elementary proof steps now establish both specified-map identities, the isomorphism criterion and the equivalent rearrangement. Status is split; no Mathlib match for the item.
- `citations.json`: one entry, quoting verbatim the tensor bifunctor/composition sentence of def-sfb-monoidal-category used in step 1. This is the only proof-node citation.
- `searches.jsonl`: six actual O2 searches, produced by msearch.py; their returned records are appended to the item without replacing the eight inherited Q145 searches.
- `report.md`: this report and signed self-review.

No new DAG nodes and no new Mathlib leaves. There was no prior item copy, proof, report or delivery result in this sandbox: only the four dispatcher markers. Before starting, I checked for an active deliver.py for this exact item; there was none. After the interrupted search I read its recorded result instead of repeating it. No direct git command, Lean edit, compiler, Lake or local DAG/preflight check was run.

## Attachments

None. Searches of lean/WeilConjectures by the exact item id and by bidual/transpose/beta/delta terminology found no project declaration stating this abstract two-category exceptional-pairing theorem. I read `WeilConjectures/SixFunctors/Etale/Derived/BoundaryDuality.lean`: its opening documentation expressly says that the canonical exchange map is not constructed; the boundary declarations assert existence of an isomorphism for geometric sheaves. That is insufficient for either specified-map identity here. I also read the interface in DoubleDualProper.lean and the closed-category InvertibleDualizing.lean declarations: those concern proper pushforward with adjoints/lax monoidal structure, or an invertible dualizing object and dualizable objects, respectively, rather than arbitrary functors s,G and a natural q on a full subcategory. No attachment is claimed.

## WANTED

None. This is an agent-written formal calculation from the hypotheses. It needs no additional literature result or omitted textbook theorem.

## What was wrong and what changed

The live node was statement-only and unsplit, created in Q145's accepted re-split of cor-weil-boundary-duality-discharge. I read that report's preserved steps 6 and 9--10 and the exact blueprint source. The current main-20261015 proof under sec-smooth-purity/sk-lem-sp-tower has the same evaluation argument as the master source under sec-six-functors/sk-prop-sf-biduality-general. The conditional abstract formulation is correct, so there is no statement dispute or statement change.

The proof is now the calculation itself. It does not cite the geometric costalk theorem as though that theorem normalized alpha, and it does not assume alpha is invertible before proving the two equations. All uses of adjunction are the natural bijections explicitly given in this item's hypotheses, all uses of symmetry are its explicit natural involution, and all uses of q are its explicit first-variable naturality. The isomorphism conclusion is proved separately by writing the actual inverses.

## What remains unfinished

Nothing in this stage-1 split. No new unsplit obligations were introduced. This delivery makes no claim to provide a Lean proof.

## Searches and existing nodes

I searched the whole DAG by transpose, currying/uncurrying, double dual, biduality, evaluation naturality and closed symmetric monoidal terminology; I ran blueprint_refs.py ancestor for this item and whole-blueprint searches for bidual, currying, opposite and transpose. The ancestor is cor-weil-boundary-duality-discharge, with no intervening nodes in this item's existing from.via. No other blueprint node states this abstract conditional exceptional-q theorem; same_as remains empty. No node was created, so there are no same-tag duplicate pairs requiring a Not duplicates section.

I read def-sfb-monoidal-category in full: its bifunctor and composition conventions are precisely what step 1 cites. I also read the existing Mathlib leaf lem-pod-closed-uncurry-laws. Its cancellation/naturality/evaluation clauses are the familiar closed-category laws with left tensor convention. This item already assumes the corresponding right tensor adjunction and all-variable naturality. The proof therefore writes the counit and naturality consequences directly in its own convention instead of introducing an orientation-conversion lemma or duplicating that leaf.

All new Mathlib queries were made through msearch.py. LeanSearch returned evaluation, curry and uncurrying declarations. Loogle returned Cartesian exponential comparisons and pointwise counits for functor categories. The first LeanFinder query returned compTranspose_eq and dual-pair evaluation identities; the second, differently phrased query returned rigid tensor-Hom naturality and Cartesian/representation comparisons. The first CategoryTheory grep had zero hits; the follow-up grep located the relevant candidate declarations. I read Closed/Basic.lean:80--125,145--220,380--412, Closed/Functor.lean:1--110 and Rigid/Basic.lean:555--577. In particular compTranspose_eq at line 403 only unfolds internal-Hom composition, the rigid evaluation lemma at line 564 assumes actual dual pairs, and expComparison_ev/uncurry_expComparison at lines 85/101 require Cartesian product preservation. None states this item's two identities for arbitrary q and arbitrary dualizing objects. All six services/commands completed successfully; none is falsely recorded as unavailable or absent. Their exact query strings and returned logs are in the item and searches.jsonl. The inherited Q145 records remain attributed to their original work, not newly claimed O2 searches.

## Review by O2

I read the standing stage-1 brief, stages/1-dag.md, GOAL.md, the three blueprint levels in SETUP.md, the worker role and this chapter/unit's records, and delivery-errors B--E whole. The chapter and unit route is unchanged. The proof's source is the second paragraph of the master's cor-weil-boundary-duality-discharge and its identical main-20261015 proof; I compared it with the source argument preserved in Q145's report. There are no new nodes whose sources need review, and no prohibited SGA source is used. I leave the unit's realized fields alone because this item is not its key statement.

Step 1 cites only def-sfb-monoidal-category, and I verified that its statement explicitly defines f tensor g as the tensor bifunctor on a pair and fixes ordinary right-to-left composition. The adjunction formula is not attributed to that definition: it is obtained from the item's assumed natural bijection, applied to a and the identity. The counit normalization is assumed in the statement. The bijection is injective without any reflexivity hypothesis. citations.json quotes exactly the definition sentence actually used.

Step 2 has no external citation: precomposition is the specified usual contravariant action, and naturality in X applied to the identity on DB gives the displayed evaluation equation. The delta equation is its defining transpose uncurried. Thus this is two direct instances of definitions, not an uncited duality theorem. It requires neither invertibility of delta nor a dualizing object in the sense of an anti-equivalence.

Step 3 specializes that evaluation equation to c:U to DP, precomposes with delta_P tensor 1, substitutes the defining delta_P transpose, and moves c through the symmetry square. I checked each source and target: every composite is P tensor U to omega_Z. The assumed opposite-currying equality then leaves b composed with sigma_{U,P} sigma_{P,U}, which is b by involutivity. Injectivity from step 1 supplies equality with beta_L. This is a three-line substitution from the assumptions, rather than a new lemma restating the clause.

Step 4 checks every inverse with its type. G(delta_L) has inverse G(delta_L inverse), and c inverse is G(delta_L inverse) after alpha_{D_TL} inverse. D(c inverse):D(U) to DD(P) is the inverse of D(c), so beta inverse is delta_P inverse after D(c inverse). Only the three listed isomorphism hypotheses are used. There is no assumption that all objects are reflexive.

In step 5 I checked the domain issue that motivated the abstract formulation: K, DK and DDK are in S_T by duality stability, and delta_K is a morphism of that subcategory because it is full. Thus q naturality at (delta_K, identity_DK) is legitimate. No tensor or internal-Hom closure of S_T or S_Z is silently used. The tensor product of delta_K and the identity is an ambient morphism, as the statement permits.

Step 6 expands beta_DK by its specified transpose. Its pairing has source sDDK tensor GDK. Precomposition with s(delta_K) tensor 1, the equation of step 5, and the defining delta_K transpose give precisely h G(ev_K sigma_{K,DK}) q_{K,DK}, with source A tensor Q and target omega_Z. Step 7 expands the other side's evaluation. Evaluation naturality for alpha_K, the delta_A transpose and symmetry naturality give ev_A(alpha_K tensor 1_A) sigma_{A,Q}. The defining transpose makes this r_K sigma_{A,Q}; expanding r_K cancels sigma_{Q,A} sigma_{A,Q}. This equals step 6. No step uses any other node's proof or a geometric existence-only isomorphism. Step 8 is just composition with the two-sided inverse D(alpha_K inverse), and its converse cancels that inverse. Both versions have the claimed types.

I tested the small cases conceptually against the actual formulas: the terminal monoidal category; the zero pairing in vector spaces; s=G=identity with q=lambda times identity, including lambda=0; a zero vector space; an infinite-dimensional nonreflexive vector space (where the equations still hold and the isomorphism hypotheses are not supplied); and one-dimensional odd super vector spaces in characteristic not 2. In the last case delta has the sign from the symmetry, and the paired symmetries cancel, so omitting either symmetry would fail. The first equation does not manufacture invertibility for the zero pairing. No finite-dimensional, rigid, additive, exact or geometric hypothesis entered the proof.

Against B--E: the statement is self-contained and unchanged, and its sole statement definition is actually the monoidal-category notion. There are no new statement-only nodes, no relabelled clauses or hidden existence claims, and all steps are explicit substitutions, naturality squares or inverse cancellations. The only cited-node claim is quoted verbatim and checked. proof_deps equals the union of uses. There are no off-unit proof-theorem tools or new edges that could create a cycle. No individual step reaches 2000 characters, and none hides a separate non-elementary assertion. During self-review I clarified the direction of the uncurrying bijection in step 1; this was a presentation correction, with the statement and formulas unchanged.

The server review_split check passed with 0 new nodes before this report was written. The full deliver.py dry run and push follow this completed self-review.
