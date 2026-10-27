# Stage-1 report: lem-sf-kunneth-second-open-substitution

## Files written

- dag/nodes/sec-six-functors/lem-sf-kunneth-second-open-substitution.json: statement, split into five proof steps; Mathlib searches found no match.
- citations.json: verbatim statements for every proof-step citation.
- report.md: this report.
- searches.jsonl: the actual search-command log.

No new nodes and no Mathlib leaves. The sandbox initially had no item or report; the live unsplit item was copied. No repository or launcher file was written, and no Lean or compiler/build command was run.

## Attachments

None. Searched the full project source under lean/WeilConjectures for the item tag, second-open substitution, proper/open terminology and Kunneth. Read SixFunctors/Etale/Derived/Kunneth/Relative.lean, lines 120–146: the relative-product theorem is sorry, and only asserts existence of an isomorphism, not these specified-morphism equalities. ModuleObjects/ProjectionFormula.lean gives abstract projection maps and some coherences but not this geometric square and substitution identity.

## WANTED

None. The argument follows the current local blueprint and the local Stacks source. No external source was downloaded or used.

## Problems corrected or clarified

The imported item had no proof. Its statement and statement dependencies are retained without change. Its existing blueprint ancestor is lem-sf-kunneth-coherence via lem-sf-product-compactification-identity. Read the chapter and relative-product unit, then the current main-20261015 coherence proof, especially its symmetry paragraph reducing to proper morphisms. This item realizes just the second-open factor of that reduction; it does not change the unit route.

The projection square is proved by an actual adjunction calculation. The proof does not infer equality from invertibility, cite the definition of a projection map as a coherence theorem, or assume that restriction is faithful on all objects. Instead, it uses the adjunction Hom bijection after identifying the source as an extension by zero. Postcomposition with the invertible restriction exchange turns both adjoints into the same map T.

An initial draft used the etale unbounded compositor plus site transport. During review I replaced it with the existing pro-etale compatible-tower normalization in lem-sf-composition-projection-mate and the explicit open-adjunction normalization in lem-sf-proper-open-tensor-compatibility. This avoids a hidden assertion that comparison functors transport the required normalization. In the second tower, for w followed by Q, the tuple (j,b,q,p) is (w,1_W,1_W,1_W); its proper maps are identities.

## Unfinished work

None within this one-level split. The cited nodes retain their own work status. No new statement-only node is needed: the argument uses existing canonical exchange, projection coherence, compositor, and open normalization statements.

## Not duplicates

No new nodes. Searched the whole DAG by proper/open, projection composition, open normalization and the relevant node names; searched the full blueprint index with `proper open`, `projection composition`, `proper/open`, and `second open`, and inspected the returned statements. The general tools were reused. The current item's more specific equality is not an attachment or Mathlib leaf.

## Review by NA

I read the item against main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, the relative-product unit and chapter, and the current projection-coherence proof at sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md. I also read literature/stacks-project/more-etale.tex, Tag 0F7B (lemma-shriek-proper-and-open), Tag 0F7J (lemma-shriek-composition, including its compatible tower), and Tag 0F7K (lemma-pseudo-functor). The blueprint omits the detailed second-open argument, so proof_origin is honestly agent. There are no new nodes whose sources need separate certification.

For step 1 I opened all seven cited nodes. The proper-permanence statement gives properness of both Q and s by base change of a. The Cartesian open-adjunction lemma gives the canonical exchange, including its counit equation; def-exchange-projection supplies exactly the counit-defined mate, so these are the same E. The proper/open tensor-compatibility statement explicitly defines its comparison as the adjunct of the inverse open-restriction comparison. In our Cartesian case its auxiliary clopen section is identity. The composition-projection-mate statement explicitly normalizes the compositor by this same compatible-tower proper/open map. Applying its two towers gives alpha_(Q,w) Gamma = alpha_(k,s). The composition theorem supplies the compactification-independent identification. The constructible-origin lemma supplies the bounded etale-origin domain, rather than extending that theorem to every pro-etale complex. I checked that no cited node depends back on this item.

For step 2 I read the open-tensor-normalization statement, including the identity-on-open-unit clause and normalized beta and gamma, and the external-tensor-normalization statement including its one-open factorization. These state the precise restrictions needed for e2. The specified projection map in def-exchange-projection is the same open tensor map. Restricting its signed version introduces a symmetry and its inverse, so its restriction is identity with all Koszul signs included. This is a short calculation from those statements and is marked elementary.

For step 3 the Cartesian open-adjunction statement supplies the Hom bijection, and projection-coherence supplies the actual base-change square and naturality, not merely the projection isomorphism. I checked the inputs are (H,J_kL), the lower square is (s,w,Q,k), and the resulting lower second input is P_kJ_kL = L. Naturality of E at e2, identity restriction of e2, and the equation from step 1 make the left adjunct equal T. The right adjunct is also T by the open unit and the restriction of Theta_k. No faithfulness of P_k on arbitrary target maps is used. Properness of Q and s ensures that the specified direct-image projection and shriek projection coincide, as the cited coherence statement asserts.

For step 4 I read fix-lem-exchanges clause 2 for horizontal pasting, which gives Ex_(a,bk) = E_H P_k(v), and its identity/compositor conventions. The projection-coherence statement gives composition and naturality, which yield the signed Theta composition after expanding the symmetries; I wrote out how the inverse symmetry pairs cancel. The only coefficient stage used is the given finite Lambda, so no completed-integral equality or faithfulness of evaluation is assumed. For step 5 the two equations from step 4 and the square from step 3 are substituted in the definition of lambda. The remaining target identification is precisely step 1 plus the associative compositor theorem; the proof displays the intermediate expression and the final composite. This is substitution and naturality, marked elementary, not an additional hidden lemma.

I checked the finite coefficients, separated finite-type morphisms, proper verticals, quasi-compact opens, and etale-origin input domain where each cited statement requires them. In particular no properness is assumed for bk, and no arbitrary pro-etale object is passed to the restricted compositor. I tested k = identity (Gamma and e2 become identity comparisons), the empty open Y (both sides factor through the zero object), and zero M or L; all formulas have the asserted source and target in these cases. The analogous identity proper map case is ordinary open tensor normalization. No extra hypothesis or change to the item statement was needed.

I checked delivery-errors B–E: there are no new nodes to be elementary, duplicated, or disguised clauses; all non-elementary ingredients are existing cited statements; all proof uses are in proof_deps; citations.json contains literal statement text; no cycle through the item is introduced. No proof step exceeds 2000 characters. Searches were run only through msearch.py, their actual signatures read, and their queries recorded verbatim. LeanFinder's first phrasing returned condensed projectivity and tensor-algebra results; its second phrasing returned ordinary pushforward compositors and over-category adjunctions. LeanSearch returned scheme-module restrictions, a proper-restriction instance, and sheaf restriction identities. None states this derived exchange/projection identity. Loogle and grep gave no hits. The old searches already present in the live node were retained as history, and the new searches have the matching sandbox log. Generic tools from other units are declared in split_report.tool_uses with their uses explained.
