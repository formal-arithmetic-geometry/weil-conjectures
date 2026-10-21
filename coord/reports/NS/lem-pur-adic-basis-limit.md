# Stage-1 worker report: lem-pur-adic-basis-limit

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-adic-basis-limit.json`: statement, split; no exact Mathlib match. Six proof steps reuse existing nodes.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's log; `prepare.py` is sandbox preparation only.

New nodes: 0. New Mathlib leaves: 0. No unit record changes: the item is an ingredient below a unit, not its key statement.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint tag, adic basis, completion/basis and scalar-extension notions. Its finite-free padic scalar-extension results concern ordinary coefficient rings and derived completeness, not these arbitrary-site completed constant sheaves. No declaration there states every clause of this item. The additional `lean/Sheaf/` search likewise gave related specialized tower constructions, not an eligible project attachment.

## WANTED

None. The source PDF and relevant Stacks source files are present.

## Statement correction

STATEMENT-DISPUTED: the last sentence said that the projection of the completed basis isomorphism at m=en *is* the quotient basis isomorphism. Literally its domain is R^d, whereas the quotient basis map's domain is the finite quotient sheaf. On the one-point site take A=B=Z, the basis (1), t=v=2, u=1 and e=1. The completed basis map is the identity of Z_2; its projection to F_2 has nonzero kernel 2Z_2, so is not an isomorphism. I replaced that sentence with the precise factorization through coordinatewise projection R^d -> (underline(A/t^n A))^d followed by the quotient basis isomorphism. This retains the intended basis, columns, scalar map and finite-level normalization. No hypothesis was changed. Bhatt-Scholze does not assert the mistaken sentence: this is wording in the agent-created refinement of Lemma 6.8.2(1).

The source gives an inverse-limit model for coefficient sheaves, not the arbitrary-ring finite-basis theorem stated here. Accordingly the proof is explicitly agent-written. It does not pretend that Lemma 6.8.2 supplies the quotient coordinates or cofinal comparison.

## Searches and existing results

Read the item's inherited NQ search results before making new searches, retaining all their records. Ran the required msearch command with LeanFinder, Loogle, grep and LeanSearch and an additional, different LeanFinder phrasing. New records use exactly the queries in searches.jsonl; all services responded. Read the hits: AdicCompletion.piEquivOfFintype/piEquivFin (Functoriality.lean:316,328) and ofTensorProductEquivOfPiFintype (AsTensorProduct.lean:180) are ordinary module-completion results. Applying them to ring sections here would require identifying constant-quotient sheaf sections with quotients of constant-ring sections, which is not asserted. They are not one-line specializations. IsLocalRing.basisQuotient (LocalRing/Quotient.lean:84, with hypotheses at line 29 and maximal-ideal notation) requires a local ring and uses its maximal ideal, so it does not state our arbitrary principal-ideal quotient assertion. The quotient assertion is instead proved explicitly in step 1.

Searched the whole DAG's statements and titles for quotient bases, constant finite products, cofinal towers and completed constant sheaves; searched the whole imported blueprint using blueprint_refs search for these concepts and for finite bases/completed constant. No equivalent blueprint node was found. The generic lem-weil-pbc-sheafification-exact and lem-pc-sites-module-sheafification-interface already give the only non-elementary sheafification inputs. The Noetherian constant-module-section-properties node is deliberately unused: the item assumes no Noetherian hypothesis. The neighboring lem-pur-constant-finite-free-products concerns scalar extension preserving products, not this tower identification. lem-weil-finite-free-completed-scalar-comparison is the parent and is not cited, preventing a cycle.

## Not duplicates

No new nodes; no new/existing pairs to justify. The coordinate quotient calculation, the explicit inverse to taking the en-subsequence, and rearranging finitely many compatible coordinates are elementary steps of this item's argument, not separate nodes or restatements of its clauses.

## Review by NS

I read Bhatt-Scholze, The pro-etale topology for schemes, PDF pp. 58-59, Lemma 6.8.2(1) and its proof: the completed sheaf is the limit of constant quotients. I read the current main-20261015 proof of lem-weil-scalar-extension-composition (under sec-proper-base-change/sk-thm-properbasechange in this snapshot), especially its first paragraph on finite free integral coefficient extensions. The item's recorded ancestor remains that blueprint node, via lem-weil-finite-free-completed-scalar-comparison. The unit is ambient six-operation typing, and this elementary coefficient ingredient introduces no alternative purity or derived route. I also read SETUP's chapter/unit/node levels, GOAL, and delivery-errors sections B-E in full. There are no new-node sources to review.

For step 1, I checked that the coordinates of t^n x are exactly t^n c_i(x), so b^{-1}(t^nB)=(t^nA)^d without any non-zero-divisor, flatness or local-ring assumption. The quotient inverse is written explicitly, and transition compatibility is an equality of representative formulas. It uses no unrecorded theorem.

For step 2 I opened every cited node's statement. def-weil-pbc-constant-sheaf defines exactly the sheafification used. lem-weil-pbc-sheafification-exact explicitly states finite-limit preservation, which suffices for the finite product; it does not supply a scalar-module assertion. For that I separately cite lem-pc-sites-module-sheafification-interface, whose statement explicitly gives sheafification over a presheaf of rings, the compatible module action and the functor on module maps. I read its source Stacks Tag 03CY, lemma-sheafification-presheaf-modules, in sites-modules.tex:815ff. I also read sites.tex Tag 00WJ, lemma-sheafification-exact, and sites-modules.tex Tags 03CN/03CO, lemma-abelian-abelian and lemma-limits-colimits-abelian-sheaves. These hypotheses are just a site, a ring presheaf and module presheaves: the constant A/t^n A ring and the quotient-coordinate modules satisfy them without extra geometric hypotheses. Applying the functor to both inverse maps proves that the resulting map is an isomorphism. Transition squares remain equal by functoriality.

For step 3 the cited constant-sheaf definition supplies functorial quotient ring maps; the cited def-pur-sheaf-inverse-limit explicitly supplies compatible-family sections, projections and the ring-sheaf case. I read the whole statement, including its final ring clause, and its Stacks sources 03DB/03CO. The ring map at m uses A/t^m -> B/v^m because t^mB=v^{em}B is contained in v^mB; e>=1 is used exactly here. The equality t^nB=v^{en}B uses that u^n is invertible. The constructed family preserves restrictions and ring operations componentwise, and uniqueness follows from the actual sectionwise projections, not a pointwise/stalk argument.

For step 4 the same inverse-limit node supplies the sectionwise description, and everything else is the displayed explicit inverse. I verified both composites and the indices: from z_{en} to z_n the source modulus is v^{e^2 n}, and the target modulus is v^{en}; from s_{em} to s_m the moduli are v^{em} and v^m. Thus no unsupported cofinality theorem or assumption that inverse limits commute with sheafification is used. Both maps preserve restrictions and operations, so the ring identification is valid on every site, including sites without points.

For step 5 the inverse-limit definition supplies compatible coordinates. The proof writes both directions of the coordinate rearrangement and checks transition compatibility by the inverses of the already established beta_n. Finite direct sum equals the sectionwise finite product by the stated coordinate inclusion/projection universal-property calculation; no new category-theoretic lemma is being hidden here.

For step 6 I checked the scalar mismatch that could otherwise be hidden: the en-coordinate of f is defined through a_{en}, whereas beta_n is linear through a_n. The map A/t^{en} -> B/v^{en}=B/t^n factors through A/t^n, and compatibility reduces a_{en} to a_n, giving precisely the required equality. The cited module-sheaf definition says componentwise R(U)-linearity is a module morphism; the cited inverse-limit definition says equality is equality of coordinates. Columns are computed at every m, and the final equation pi_{en} Psi = beta_n (pi_n)^d is the corrected conclusion, not a claim about surjectivity of an inverse-limit projection.

I tested d=0 (B is the zero module/ring), zero rings, t=v=0, unit t or v (the relevant limits are zero), nilpotent parameters and e=1. For e>1 the reindexing still uses only m<=em and n<=en. No separation, completeness, Noetherianity, regularity, enough-points or non-zero-divisor assumption is needed. Smallness is already in the item and ensures the sheaf/module categories and the countable diagrams fit the stated limit input. Every proof step is below 1000 characters, and I found no hidden non-elementary sublemma. There are no off-unit non-Mathlib tools: both sheafification inputs are existing Mathlib leaves. No SGA source is used.

The quotations in citations.json were checked as verbatim substrings of the actual cited statements. Proof dependencies equal exactly the union of the uses lists. The corrected statement and proof preserve the source and created/blueprint metadata, with same_as filled after the whole-blueprint search.

## Unfinished work

None in the mathematical split. The final dry run and push are performed with the mandated delivery command; their outcome is reported in the final one-line delivery message.
