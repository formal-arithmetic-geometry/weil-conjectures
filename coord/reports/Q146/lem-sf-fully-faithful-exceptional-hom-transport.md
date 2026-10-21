## Files written

- `dag/nodes/sec-six-functors/lem-sf-fully-faithful-exceptional-hom-transport.json`: statement item, split into five proof steps. The statement is unchanged. Mathlib supplies the individual adjunction equivalences and the fully faithful unit theorem, but not this entire specified comparison and origin normalization as an exact or one-line specialization.
- `citations.json`: a verbatim statement quote for every node cited by every proof step.
- `searches.jsonl`: five actual searches through the prescribed msearch command. All five services/queries returned answers, which were read.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record needs changing: this auxiliary created node is not its unit's key statement.

## Attachments

None. The exact blueprint-tag search in `lean/WeilConjectures` returned no declaration. Concept searches in the project found related adjunction-mate formulas, geometric boundary-duality theorems, and invertibility of units, but none states all clauses of this abstract four-category comparison under exactly these hypotheses. In particular `CategoryTheory.ObjectProperty.isIso_unit_app_of_lift` in ClosedImmersionStages only gives invertibility of a corestricted fully faithful unit. The geometric internal-Hom exchange in BoundaryDuality has different hypotheses and conclusions.

## Wanted literature

None. All sources used are present locally. No SGA source was used.

## What needed work

The item arrived unsplit with its full abstract statement and prior Mathlib search records from Q103. There was no earlier sandbox split, report, citation file, or search log to resume. I retained the complete statement, prior searches, provenance, source, and blueprint reference, and appended the searches actually run for Q146.

The source named Tag 0DV0, lemma-compose-counits. I read that proof, which gives the composite-adjunction principle by explicitly composing Hom bijections; it does not by itself state the item's fully faithful normalization. I also read Tag 0037 (definition-adjoint and the immediately following unit/counit formulas) and Tag 07RB (lemma-adjoint-fully-faithful). The split is therefore honestly marked agent-origin: it supplies the actual normalization calculation rather than attributing the complete item to 0DV0.

The nearest blueprint ancestor is `cor-weil-boundary-duality-discharge`, reached through `lem-weil-boundary-proetale-projection-comparison`. I read its current-brief snapshot statement and proof in main-20261015, especially the second paragraph defining the boundary comparison by evaluation and adjunction. The present calculation serves that normalization and changes neither the unit route nor the chapter. Whole-blueprint searches for fully faithful comparisons and Hom transport found no equivalent blueprint statement. Existing generic tools are reused rather than creating new nodes for the item's own clauses.

## Review by Q146

I checked the item against Categories Tags 0037, 07RB and 0DV0 with their statements and proofs open. I checked both cited DAG statements in full: `lem-weil-pbc-adjunction-of-natural-bijection` explicitly gives the naturality equations, identity formulas for unit/counit, and the forward unit formula for the Hom equivalence; `lem-sp-adjunction-unit-fully-faithful-left` explicitly states that the unit of a specified fully faithful left adjoint is invertible. I also read Mathlib Adjunction/Basic.lean lines 160–182, Adjunction/FullyFaithful.lean lines 62–76, and Adjunction/Restrict.lean lines 35–80. The latter needs an ambient adjunction and both restriction squares; it cannot be applied in one line to manufacture the restricted Hom family of this item.

Step 1 uses the first cited statement for the two given adjunction bijections, not to choose replacement adjunctions: its formulas give alpha(w)=R(w) composed with j and beta(mu)=identity with the given normalization. Step 2 uses the naturality equations that the same node actually states. Each constituent is bijective by an explicit hypothesis or by inversion of b; the displayed two naturality equations are obtained by substituting naturality of b, alpha and beta and functoriality. Thus no general theorem about transported adjunctions is hidden here.

Step 3 uses the fully faithful left-adjoint unit node with L=C_T and its specified R. Full faithfulness of C_T is exactly a hypothesis of the item; no essential-surjectivity or full faithfulness of R is needed. Applying G_e and C_Z to the inverse identities gives the displayed inverse of o_N directly. This is the sole non-elementary generic theorem used, and it is already a Mathlib leaf.

Step 4 uses the first node's forward unit formula and right-variable naturality, under the same specified adjunctions as in Step 1. Full faithfulness supplies v of exactly type F_e H to N from q composed with b_H; naturality of j identifies its alpha image as j_N composed with v. Applying beta and C_Z gives h(q)=o_N composed with C_Z(beta(v)). Cancelling the inverse of o_N proves equality with the required entire four-arrow chain. This short substitution is in the proof, not hidden in a new lemma.

Step 5 uses the formulas already established in Steps 1–4: set v=mu, obtain beta(v)=identity, and use injectivity of h for uniqueness. Its description as a counit is precisely the inverse image of the identity after the origin identification, as the statement requires. No claim is made on non-origin objects. Each citation is a statement-level use, and citations.json copies that statement verbatim. All proof steps are below 800 characters; no long step hides a comparison lemma.

I checked the B–E return cases individually. There are no new nodes, so there is no duplicated clause, unsearched leaf, or unsupported new notion. The statement introduces every category, functor, comparison, unit and counit. The proof uses only the two cited theorem statements and the given definitions/hypotheses; it neither cites a proof-only construction nor relies on a bare source tag for a non-elementary theorem. The source tags and labels are checked in the local Stacks tag map. Both cited nodes are existing Mathlib leaves, so they are generic tools and do not change the unit's proof route. No statement, source, inherited blueprint field, or maintainer-owned audit field was altered. Each computation has been type-checked on paper with right-to-left composition.

As edge cases, taking all comparisons and b to be identities recovers the original adjunction bijection and its counit; empty categories make the corresponding quantified clauses vacuous. A non-essentially-surjective test is X_e=T_e=Set, X_p=T_p=Set×Set, C_Z=C_T sending A to (A,empty), R the first projection, and F_e=G_e=F_p=identity. The hypotheses hold; the Hom family is exactly Hom((H,empty),(A,B))=Hom((H,empty),(A,empty)). It holds even when B is nonempty, while identity on Set×Set has no adjunction to the functor (A,B)↦(A,empty). This verifies why the restricted origin-object formulation must be retained. Choosing a nonidentity natural automorphism b in a one-object abelian group category checks the inverse direction: the counit preimage uses b inverse, as the statement and Step 5 do. No statement dispute was found.

## Unfinished work

None in the requested one-level split. The required dry run and push are performed after this report is written; their outcome is reported by the delivery command and the final answer.
