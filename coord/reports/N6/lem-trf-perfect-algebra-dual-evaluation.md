# Worker report: lem-trf-perfect-algebra-dual-evaluation

## Files written

- dag/nodes/sec-trace-formula/lem-trf-perfect-algebra-dual-evaluation.json: statement split into five proof steps, using existing nodes only; not a Mathlib leaf.
- citations.json: one verbatim statement quote for every step/node pair.
- searches.jsonl: actual search-command output records. The five fresh searches supplement the inherited searches without deleting them.

No new nodes and no new Mathlib leaves. No unit realization changes: this auxiliary node is not the unit's key statement. The full imported statement, statement dependencies, source, creation provenance, and blueprint ancestry are preserved.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint id and for perfect-dual, evaluation, precomposition and coinduction notions, and inspected the nearby PerfectRHomEvaluationIsomorphisms and OrdinaryEvaluationPrecompositionNaturality interfaces. They concern sheaf evaluation or ordinary finite-projective models, not the entire asserted derived B-linear comparison. There is no exact project declaration to attach.

## Wanted

None. The sources used are present in literature/stacks-project/.

## Findings and corrections

The node was a statement-only child of the polynomial diagonal reduction. There was no existing sandbox split to retain. I retained its statement verbatim. In particular, B is perfect as an S-complex, not necessarily flat or projective as an S-module, and V is arbitrary in the unbounded derived category. A bounded finite-projective S-model need not have a strict B-action; the proof therefore constructs the morphism in D(B) by the existing bimodule adjunction and proves invertibility after restriction.

The split uses the existing biduality node only for dual perfectness and the canonical bidual isomorphism. Its statement does NOT assert arbitrary-coefficient tensor evaluation. I take that separate fact from lem-trf-perfect-source-evaluation-quasi-isomorphism. This distinction repairs the tempting C4 shortcut of citing biduality alone for all of Stacks 07VI. Likewise conservativity and evaluation at 1 come from lem-trf-derived-coinduction-adjunction, not merely the definition of coinduction. The formula epsilon(bz)=z(b) identifies the particular adjunct, so no unspecified isomorphism substitutes for alpha.

## Searches and reuse

I read Stacks more-algebra.tex, Tag 07VI (lemma-dual-perfect-complex), Tag 0A66 (lemma-RHom-out-of-projective), Tag 0ATK (lemma-internal-hom-evaluate-tensor-isomorphism), and Tag 0BYN (lemma-internal-hom-diagonal-better); dualizing.tex Tags 0A70/0A71 (lemma-right-adjoint, lemma-RHom-ext); and dga.tex Tags 09LN/09LT (lemma-tensor-hom-adjunction, lemma-tensor-hom-adjoint). These are ordinary module derived-category sources, not SGA.

DAG searches for 07VI/0A66, perfect evaluation, biduality and conservative scalar restriction found all four needed existing trace-unit results. Whole-blueprint searches for perfect, coinduction, dual evaluation, precomposition and 07VI found no blueprint node stating the present algebra-action enhancement. The ancestry command confirms lem-trf-local-term-locality; the current latest blueprint unit and that ancestor were read. The long ancestry remains the relative-duality input to normal-cone specialization, with no change to the geometric unit route.

Fresh leanfinder searches used both an algebra-action wording and a dualizable-complex wording. LeanSearch returns dualTensorHomEquivOfBasis, dualTensorHomEquiv, reflexivity and ordinary tensor-product results. The second leanfinder wording returns rigid-category tensor-Hom identities and ModuleCat.ihom_coev_app. Loogle's combined MonoidalClosed/HasLeftDual query has no hits. The prescribed grep command returns coextendScalars and restrictCoextendScalarsAdj in ModuleCat/ChangeOfRings. I read Contraction.lean around lines 160-215 and ChangeOfRings.lean around lines 590-630. These are useful ordinary-module or categorical ingredients, but none specializes in one line to the specified unbounded D(B) arrow from S-perfectness. All query strings and outcomes are recorded exactly in the node and search log.

## Review by N6

I checked the item against the complete statements in the cited Stacks places. Tag 07VI works over an arbitrary commutative coefficient ring and supplies a perfect dual and the canonical bidual arrow; 0ATK case (1) needs only a perfect Hom-source, so after applying 07VI to B it applies to UE with arbitrary coefficient V. Tags 09LN/09LT supply the bimodule tensor-Hom adjunction; the already-existing DAG enhancement explicitly fixes precomposition action, evaluation counit, independence of representatives and naturality. Tags 0A70/0A71 identify the actual underlying S-object and the evaluation-at-1 normalization. None introduces flatness or Noetherianity. I read every cited node's full statement, not only its title or proof.

Step 1 uses lem-trf-derived-coinduction-adjunction for UE=RHom_S(B,S) and the evaluation-at-1 counit, and lem-trf-perfect-complex-derived-biduality for perfectness of UE and invertibility of d. Its braided-monoidal wording is satisfied by the ordinary Koszul symmetry of D(S); no arbitrary braiding is silently substituted. Step 2 uses the K-flat resolution theorem on the small one-object site, and the K-injective existence theorem twice, once for S and once for F tensor J. The K-flat F represents arbitrary V; since J represents the tensor unit, F tensor J represents V. The perfect-source evaluation node states both invertibility and the exact normalized comparison, and its source-perfectness hypothesis was established in step 1. The K-flat/K-injective results are generic off-unit tools, declared in split_report.tool_uses; they do not replace a geometric step.

Step 3 is a composition of the two already cited isomorphisms and the Koszul symmetry. Its uncurrying calculation uses the stated canonical bidual map and the stated canonical perfect-source evaluation map; it proves the identification explicitly by evaluating d(b) on z. There is no new perfect-evaluation lemma hidden here and no finiteness assumption on V. Step 4 reads the actual bimodule adjunction statement: it gives the adjoint arrow in D(B), its scalar-restricted transpose, and its precomposition action. The coinduction theorem and definition state (bz)(b')=z(b'b), so setting b'=1 proves epsilon(bz)=z(b). This equality holds on the coinduced K-injective model, and pulling it back along tensor resolutions leaves it an equality; injectivity of the tensor-Hom bijection identifies U alpha with beta. Thus a declaration only of full faithfulness, a definition alone, or an unspecified derived isomorphism is not being used to supply a stronger theorem. Step 5 uses adjunction naturality for all derived u and the expressly stated conservativity to conclude in D(B); its naturality square is written out through epsilon tensor u.

For B1--B10 no new node is proposed: there is no statement-only child hiding a proof, no new definition, no duplicate, and no clause of the item relabelled as a lemma. For C1--C8 every non-elementary input is an existing cited statement, the union of uses is proof_deps, and each has a verbatim quote in citations.json. The elementary steps are compositions, injectivity of adjunction, the displayed evaluation-at-1 substitution and naturality of a fixed adjunct; they are not appeals to unstated duality. For D1--D5 the steps carry the argument rather than applying a restated item. Every step is under 2000 characters. For E1--E7 I checked the coefficient ring, the object UE (not E as a perfect B-object), and the unbounded coefficients at each application; no theorem is applied with a stronger hypothesis than has been established.

I tested the statement on q=id (E=S and alpha is the unit comparison), B=0 (both sides zero), V=0 (both sides zero), and S=Z, B=Z/p with V=Z and V=Z/p. In the latter nonflat example E is B[-1], so its S-bidual is B; derived Hom from E recovers B derived tensor V, including the nonzero Tor degree for V=B. This checks why an ordinary tensor or Hom calculation would be insufficient. Arbitrary shifts and unbounded V are allowed by 0ATK, rather than reduced to bounded coefficients. No mathematical correction to the item was required, and no source error was found.

## Not duplicates

No new nodes were created. Existing 07VI and 0ATK nodes are reused, and the coinduction-tensor theorem is not mistaken for the present dual-evaluation arrow: its Hom-source is B, whereas here the Hom-source is E=RHom_S(B,S).

## Unfinished work

None in the stage-1 split. No Lean was written and no compiler, Lake or local DAG check was run. The required server dry run and direct push are the remaining delivery operations.
