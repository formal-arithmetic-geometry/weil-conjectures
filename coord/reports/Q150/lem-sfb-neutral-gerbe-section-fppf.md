# Stage-1 worker report: lem-sfb-neutral-gerbe-section-fppf

Group Q150, direct delivery, 2026-10-23.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-neutral-gerbe-section-fppf.json`: item, four proof steps, status split; original statement retained verbatim.
- `dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-classifying-stack-flatness.json`: one new statement-only prerequisite, status unsplit; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every cited node in every item step.
- `searches.jsonl`: actual search-command log; item and new-node searches reused from this turn, none invented.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id and the gerbe, classifying-stack and groupoid notions. No declaration proves the item or the new prerequisite. General classifying-morphism occurrences concern schemes and Picard functors and do not qualify as attachments.

## WANTED

None. The full sources used are present locally: `literature/stacks-project/stacks-morphisms.tex` Tag 06QG (lemma-gerbe-with-section), `criteria.tex` Tag 06PL (lemma-BG-algebraic), Tag 06FH (lemma-flat-quotient-flat-presentation), `algebraic.tex` Tag 04T4 (lemma-map-space-into-stack), and `stacks.tex` Tag 046N (lemma-characterize-essentially-surjective-when-ff). The existing fppf-descent bridge supplies the etale-stack convention used by the project's definition.

## Findings and changes

The item was unsplit and the sandbox was empty. The imported statement is correct; no STATEMENT-DISPUTED correction is needed. The proof follows 06QG, retaining its neutral quotient argument rather than assuming an automorphism group is smooth. The new lemma is exactly the converse implication of 06PL. It concerns the group's structural morphism, not the section of a gerbe, so it is neither a clause copied out of the item nor the entire item under another name. It can be used for any group algebraic space over any algebraic-space base, without a chosen gerbe or section.

The chapter record, unit record, SETUP's three levels and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` section and direct-images proof were read. This is the supporting neutral-section prerequisite of the recorded alteration/moduli route under direct-images proof (3), not a change of that route. The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor lem-sfb-neutral-gerbe-section-fppf` explicitly returns None. The new node therefore preserves that value, prefixes the item to the inherited via list, and specifies precisely the 06QG-to-06PL substep in from.place. No chapter or unit record is written.

## Searches and reuse

Before creating the new node I searched the whole DAG by tags 06PL/06QG/06FH and labels BG-algebraic, flat-quotient-flat-presentation and map-space-into-stack, and by gerbe, classifying-stack, quotient and groupoid terms. Blueprint searches `gerbe`, `classifying`, `classifying stack`, `06PL`, `046N` and `flat groupoid` found no blueprint version of the new claim. Existing nodes for the self-relation quotient, local essential surjectivity, fppf stackification and flat-groupoid quotient are used instead of recreated. The existing stack-Isom theorem is not substituted for flatness: local finite type alone would not imply it.

The new node's actual Mathlib searches are recorded verbatim in its JSON and in searches.jsonl: LeanSearch, two LeanFinder phrasings, Loogle and grep. The semantic hits were Flat, LocallyOfFinitePresentation, smooth-implies-lfp, universally-open-of-flat, and scheme flat descent. I read the scheme declarations in `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:42`, `FinitePresentation.lean:45` and `FlatDescent.lean:178`. Their objects are schemes or commutative rings, not group algebraic spaces or algebraic classifying stacks. Loogle and the whole-Mathlib gerbe/classifying-stack grep returned no hits. The second semantic phrasing also returned only scheme/ring facts. The item's own new searches likewise found no match. All services answered; none was treated as unavailable or as an unrun negative search.

## Not duplicates

No existing node carries Tag 06PL in its source. The following nearby results were read rather than inferred from their titles:

- lem-sfb-algebraic-classifying-stack-flatness vs lem-sfb-neutral-gerbe-section-fppf: the new node deduces flatness and local finite presentation of a group from algebraicity of its classifying stack; the item constructs the neutral equivalence from a gerbe section and concludes properties of that section.
- lem-sfb-algebraic-classifying-stack-flatness vs lem-sfb-flat-groupoid-algebraic-quotient: the existing node assumes flat locally finitely presented source and target maps and concludes algebraicity and presentation properties; the new node recovers those hypotheses for a trivial-action groupoid from algebraicity.
- lem-sfb-algebraic-classifying-stack-flatness vs lem-sfb-flat-affine-action-stack-presentation: the existing result is over a field with an affine finite-type group and an affine action; it cannot deduce flatness for an arbitrary group algebraic space over an arbitrary base.
- lem-sfb-algebraic-classifying-stack-flatness vs lem-sfb-flat-inertia-algebraic-space-quotient: the existing node assumes flat locally finitely presented inertia and constructs a quotient; it does not prove that assumption from algebraicity of a classifying stack.

## Review by Q150

I checked delivery-errors B through E with the node statements and the cited sources open. The item agrees hypothesis by hypothesis with 06QG(3), specialized from an algebraic-space base to a scheme: the section's specified 2-isomorphism is retained, and there is no extra finite-type, smoothness, separation, Noetherian or quasi-compactness hypothesis. The new node agrees with the converse of 06PL, whose group is initially an arbitrary group algebraic space over B. Its trivial-action quotient is defined explicitly through an fppf stackification; it has a statement only and no embedded proof. Its notions cite the relevant definition nodes, and its searches were performed before writing it.

Step 1 uses the statement of lem-sfb-etale-smooth-atlas-fppf-descent for fppf object and arrow descent, with exactly the atlas and diagonal furnished by def-sfb-algebraic-moduli-stack. It uses the statement of lem-sfb-self-relation-quotient-embedding for representability of R, all groupoid operations and the canonical fully faithful quotient map commuting with x. That theorem assumes no fppf property of x, so this use is not circular. Applying a to an arrow gives equality v=w because the target scheme is discrete; the specified ax isomorphism identifies the endpoints. This is the written elementary calculation identifying the self-relation with the automorphism group, including its multiplication, not a hidden quotient or smoothness theorem.

Step 2 uses lem-sfb-groupoid-stackification-local-description only for existence of the quotient as an fppf stack. The gerbe hypothesis itself, applied to x(ay) and y over T, produces its local images. Both stack assumptions and full faithfulness required by lem-sfb-stack-fully-faithful-local-equivalence are now available; its statement really supplies a pullback-compatible equivalence, not just Yoneda full faithfulness. Algebraicity is invariant here directly by the atlas definition: composing an atlas with a quasi-inverse gives the same algebraic-space scheme tests, and the unit/counit give the diagonal identifications. I wrote this argument out instead of invoking an unrecorded geometric comparison lemma.

Step 3 uses only the statement of the new 06PL prerequisite. The base is V, G is a group algebraic space by step 1, and its quotient is algebraic by step 2. Flatness and local finite presentation are conclusions of this theorem, never prior assumptions on G or on x. The two groupoid projections really coincide with G to V.

Step 4 uses the exact presentation clause of lem-sfb-flat-groupoid-algebraic-quotient. Both required projections are flat and locally finitely presented by step 3. Its conclusion contains representability as well as surjectivity, flatness and local finite presentation. The quasi-inverse identifies the two fibre products over each test scheme, so all four properties pass to the specified x, and not merely to an unrelated atlas. This is the elementary invariance of the stated scheme-test definition, with the actual comparison maps described. Every cited statement is quoted verbatim in citations.json; no source's proof is silently used as its statement.

For small cases, the trivial group gives the identity section and identity presentation; an empty base is harmless and every assertion is vacuous on its empty tests. Over a characteristic-p field, G=mu_p gives a non-smooth but flat finite-presentation group and an fppf, not necessarily smooth, neutral-section map. This checks that no step has introduced a smooth-group hypothesis. A group lacking flatness or local finite presentation cannot satisfy the new node's algebraicity hypothesis, exactly as 06PL asserts; no arbitrary group's classifying stack was presumed algebraic. None of these statements requires quasi-compactness. I also checked that the new node is strictly the independent group-flatness input, existing special cases are not duplicated, and all four non-elementary steps are below 2000 characters (878, 871, 444, 660). There is no hidden long lemma or SGA source. No other worker or agent was started; this is the authorized direct-delivery self-review.

## Unfinished work

The new 06PL prerequisite is intentionally left unsplit for the next DAG item. No other part of the assigned split remains open. The required server checks and delivery outcome are recorded by the delivery invocation.
