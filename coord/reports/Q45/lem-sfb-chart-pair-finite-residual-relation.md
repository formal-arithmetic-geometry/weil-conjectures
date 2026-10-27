# Q45: lem-sfb-chart-pair-finite-residual-relation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-chart-pair-finite-residual-relation.json: existing statement split into six local steps. Its mathematical statement and statement dependencies are unchanged. No new nodes; no new Mathlib leaves.
- citations.json: twelve entries, one for every step/node pair, with verbatim substrings checked against the live node statements.
- searches.jsonl: actual msearch results for this item, retained by the search tool.

## Attachments

None. Searches for the blueprint tag and algebraic-space/residual-relation terminology in lean/WeilConjectures found no declaration stating this result. Existing finished Mathlib input lem-sfb-residue-field-point-monomorphism is reused, not recreated or claimed as an attachment for the item.

## Literature wanted

None.

## Issues and corrections

The imported node had no proof. Its source is correct: Stacks decent-spaces.tex Tag 03JU (lemma-R-finite-above-x), the initial pair-fibre discussion and the paragraph proving (2) implies (3). The latter argument is local at the chosen chart point, so the stronger universal hypothesis (2) of the full Stacks lemma is unnecessary here. Neither a surjective chart nor a finite chart fibre nor quasi-compactness of U is used. There is no statement dispute.

I read the latest blueprint direct-images statement/proof and the unit and chapter records. The inherited provenance chain describes supporting alteration/moduli inputs of clause (3). The ancestor command returns None for this item; the inherited null from.node and its detailed place/via are preserved, rather than inventing a new ancestor. Blueprint searches for residual, 03JU, finite relation, monomorphism into fields and 03DP found no imported node giving this item. DAG searches did find the exact supporting monomorphism and etale-field lemmas, so none was recreated. No chapter or unit record was changed.

Mathlib searches ran through msearch: two LeanFinder phrasings, LeanSearch, Loogle, and a source grep. All services answered. The hits concern schemes, etale definitions/permanence and finite-morphism fibres, not this theorem about a residual relation over an algebraic space. The grep for AlgebraicSpace and residueField/relation terminology had no hits. Existing historical searches in the item were retained, and these actual new searches appended verbatim with their results. No search or result was invented.

## Review by Q45

I read Stacks Tag 03JU in decent-spaces.tex with the source's actual factorization u times_X u -> u times_X U -> u in view. I also read schemes.tex Tag 03DP (lemma-mono-towards-spec-field) and morphisms.tex Tag 02GL (lemma-etale-over-field), which are the classification inputs the source invokes. There are no new nodes needing a separate source audit. For every cited node I opened its full statement, not just its title or proof; the selected verbatim quotes are in citations.json.

Step 1 uses lem-sfb-residue-field-point-monomorphism exactly for monicity of the canonical point map, including non-closed points. def-trf-algebraic-space supplies the representable diagonal, so both residual and chart relations are schemes even though the residual point map need not be etale. lem-trf-space-fibre-products-etale-covers supplies the sheaf fibre-product universal property. The induced map E -> R is proved monic by cancelling i separately in each coordinate; no theorem about underlying topological fibres is silently substituted for the scheme fibre product.

Step 2 uses the explicit equivalent field-point criterion (1) and universal injectivity (2) in def-weil-radicial-morphism. The monomorphism established in step 1 satisfies (1) for all fields, hence its underlying map is injective. This is a theorem contained in that node's statement, not something inferred from the name radicial. The two projection equations place its image in the finite hypothesized pair fibre. Only injection into that fibre is needed; no unexplained identification of underlying sets of fibre products is used.

Step 3 uses def-trf-algebraic-space for precisely its definition of representable etale: base change to T is a scheme etale over T. This gives both D_1 and D_2 without a covering assumption. The same residue-point monomorphism statement makes E -> D_nu monic by the written coordinate cancellation, so base change of monomorphisms is not an uncited input.

Step 4 uses lem-weil-pbc-etale-fibre-discrete-separable-points with the actual etale scheme morphism D_nu -> Spec K. The fibre at the unique point is D_nu itself because its residue-field representative is the identity of Spec K. Its statement gives the disjoint field decomposition, including infinite indexing. The full statement of lem-sfb-monomorphism-into-field-coproduct then gives an isomorphism over D_nu with a subset of these components; it applies to arbitrary schemes and arbitrary field families, and requires neither finite type nor quasi-compactness. Both nodes say exactly these things; neither depends on the item.

Step 5 uses the open component inclusions in lem-weil-pbc-scheme-coproduct-family. A union of those components with restricted structure sheaf is an open subscheme, so def-weil-open-immersion gives that its inclusion is open. Parts (1) and (2) of lem-weil-pbc-etale-composition-cancellation state that open immersions are etale and composites of etale maps are etale. This proves each projection by its own D_nu factorization, avoiding an implicit invariance-under-swap argument. This step is elementary assembly of the cited statements, not an unproved new lemma.

Step 6 uses only the definition of quasi-compactness in def-weil-pbc-quasi-compact-scheme: the finite point-set admits a finite subcover by choosing one covering member for each point. Both affine-open inverse images are then either empty or E, since a field spectrum has only its empty and whole opens. This is the exact quasi-compactness clause in the item; no separatedness assertion is needed.

I tested the empty source for the auxiliary monomorphism classification, the one-component identity chart over a field, a non-closed generic chart point, and an infinite disjoint-union chart with the selected point on one component. Empty E is harmless to the proof (in this self-relation situation it actually has a diagonal point). The infinite chart example confirms why global quasi-compactness of U is not an assumption. No reducedness, perfection, algebraic closedness, finite type or Noetherian hypotheses were introduced. A finite subset of the relation can be non-closed in R; the proof uses only injectivity into it, not a closed-subscheme assertion.

I checked delivery-errors B through E point by point. There are no statement-only new nodes, duplicate nodes, relabelled clauses, hidden standard lemmas, source-only proof citations, proof-of-another-node citations, missing hypotheses, or newly created cycles. The explicit arguments for monicity and finite-space compactness are elementary steps. Every non-elementary invocation is a cited statement. All steps are under 600 characters, so none exceeds the 2000-character long-step threshold. Off-unit general scheme inputs are declared in split_report.tool_uses with their exact purpose; they do not replace the unit's route. No SGA source was used.

## Not duplicates

No new nodes. In particular, reuse lem-sfb-residue-field-point-monomorphism and lem-sfb-monomorphism-into-field-coproduct; do not duplicate the existing Tag 01L6 and Tag 03DP inputs. The existing Tag 03JU node lem-sfb-finite-point-self-relation-field-monomorphism proves (3) implies (4), whereas this item proves the local pair-fibre to (3) implication; it is not used to prove itself.

## Unfinished work

None in the one-level split. Existing supporting unsplit statements retain their own independent work queue entries.
