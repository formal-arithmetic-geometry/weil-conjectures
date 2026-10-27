# Q140 stage-1 delivery: lem-sfb-open-square-closed-unit-triangle

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-open-square-closed-unit-triangle.json`: statement, split; seven proof steps using existing nodes. Statement and statement dependencies unchanged. Fresh Mathlib searches find no exact match.
- `citations.json`: one entry for each of the 18 step/node citations, quoting the cited statement verbatim.
- `report.md`: this report. The search command maintains `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint tag, item id, localization/recollement and closed-unit names. Read the pro-etale adic Localization module and inspected the ModuleObject source searches: the available adic/finite localization statements have different coefficient categories and constructibility/field hypotheses. None states this arbitrary condensed-ring ordinary internal-module result with every specified map. A sorry-bearing or specialized declaration was not treated as an attachment.

## WANTED

None. All source material needed for the assembly is available.

## Findings and changes

The live node was unsplit with no proof and no Lean audit attachment. Its statement is correct as written; no STATEMENT-DISPUTED change is needed. The blueprint direct-images paragraph (3) motivates the surrounding finiteness argument but does not print this extracted formal lemma. This proof is therefore explicitly agent-written, using the actual Stacks localization sequence and existing DAG lemmas, rather than attributing a nonexistent theorem to that paragraph.

The chapter describes ordinary pro-etale internal modules as well as completed coefficient categories. The unit id is shared with an older six-functors unit record; I read both that record and the current six-functors-basics direct-images proof. This item supplies a formal localization input and does not alter either unit's finiteness route. The off-unit inputs are generic tools declared in `split_report.tool_uses`.

`tools/blueprint_refs.py ancestor lem-sfb-open-square-closed-unit-triangle` returns None for the current live chain. I preserved that null ancestor and the existing via chain; the already specific from.place was retained. Whole-blueprint searches for localization, closed unit, ring-sheaf and open-closed found the existing ringed localization sequence and the completed/all-stages triangle, but no statement equal to this item. The latter has different coefficient and scheme hypotheses and is not substituted for the arbitrary condensed-ring statement. No node was created or duplicated.

Fresh logged searches: two LeanFinder phrasings, LeanSearch, Loogle and source grep, all returned successfully. The first LeanFinder query found affine-localization algebra and tilde modules; the second found generic SES triangles. LeanSearch found derived adjunctions. Loogle found `DerivedCategory.triangleOfSES` and distinguishedness/map clauses. These are ingredients already represented in the DAG, not one-line proofs of the item. The grep hits were monoidal closed units and a topological unitary lemma, not geometric closed units. Read Mathlib DerivedCategory/ShortExact.lean (naturality, triangle construction, distinguishedness), HomologySequence.lean (isIso_iff), and Functor/Derived/Adjunction.lean for the candidate ingredients. Existing search history on the live node was retained; newly recorded searches are precisely the sandbox log queries.

## Not duplicates

No new nodes. The ring-sheaf sequence is reused through `lem-weil-pbc-proetale-ringed-open-closed`, not recreated. `prop-sf-open-closed-triangle-all-stages` is a completed/constructible finite-coefficient-stage result, so it is not used to change the ambient category. The exact internal operations comparison, unbounded open/closed calculus, K-injective word model and canonical module shifts are also reused without moving this item's clauses into new nodes.

## Review by Q140

I read the item, the current blueprint direct-images paragraph (3), the recorded chapter and unit, and every cited node's entire statement. For the source argument I read Stacks proetale.tex at `lemma-open-immersion` (09BN), `lemma-ses-associated-to-open` (09AH), and `lemma-closed-immersion-complement-retrocompact-exact` (09BM); derived.tex at `lemma-derived-canonical-delta-functor` (0152), `lemma-right-derived-exact-functor` (015F), `proposition-derived-functor` (05SE), `lemma-negative-vanishing` (05TC), and `lemma-cohomology-homological`. I also read the current alpha-isomorphism and module-pullback-exactness blueprint statements, the scalar-six pullback proof, and the Mathlib source named above. There are no new-node sources to review. No SGA source is used.

Step 1 uses exactly the Noetherian-open-subscheme lemma: its conclusion gives both Noetherianity of V and quasi-compactness of each affine intersection with W. Thus b is a quasi-compact morphism, not merely an open immersion with quasi-compact domain. This is the precise hypothesis in 09AH and in the ringed open/closed node. The proof makes no separation assumption on Y.

Step 2 uses alpha-isomorphism for arbitrary condensed rings, not the narrower admissible-coefficients proposition. The internal-module operations transport node expressly identifies the specified adjunction units and counits under exact equivalences and includes extension by zero. The ringed open/closed node expressly gives exactness of closed direct image, exact open extension and the exact sequence whose arrows are the counit and unit. The pullback-exactness node expressly concerns arbitrary condensed rings and arbitrary scheme morphisms. Its hypothesis therefore covers i, h and b. The complement is the given reduced closed complement, which is allowed by the ringed theorem. The source's exactness condition is quasi-compactness of b, verified in Step 1.

Step 3 uses the SES-complex triangle node for both distinguishedness and naturality, the exact-derived-functor node to identify h_* with Rh_* and exact functors with their termwise realizations, and the exact-open-closed calculus for descent of the actual units/counits. All its hypotheses were supplied in Step 2: both adjunctions, invertible open unit/closed counit, mixed zeros and the exact sequence are in the ringed open/closed statement. Naturality of the SES makes a complex sequence; exactness implies its functors invert quasi-isomorphisms. This is why the natural triangle descends, without a functorial-cone assertion for arbitrary triangulated categories.

Step 4 does not cite an open-extension unit as if it were the direct-image counit. The word-model node supplies K-injective representatives and canonical word evaluation for arbitrary condensed rings. The pro-etale open-restriction-counit node applies to arbitrary ring sheaves; for f=b and target open W, its fibre products are W and the restricted maps are identities. Its explicit counit equation gives the underived isomorphism at I. The derived-adjunction node supplies the counit comparison, so the map on the resolution is the actual derived counit, followed by the inverse resolution isomorphism. The internal/sectionwise comparison of Step 2 ensures it has the internal coefficient action. The explicit replacement arrow is epsilon composed with b_! of the inverse counit. Thus no arbitrary identification changes the closed-unit arrow.

Step 5 cites the canonical module-derived-functor shifts node: its statement actually says that P_u and G_u are exact functors for every scheme map and arbitrary commutative condensed ring. Those are precisely Li^* and Rj_* here, and its comparison identifies Li^* with exact termwise i^*. Applying the composite preserves the three natural maps and shift comparison. No finiteness or constructibility is needed.

Step 6 uses Grothendieckness of arbitrary ring-sheaf modules and the exact internal/sectionwise equivalence, plus the specified pushpull adjunction, to verify the categories and left exactness assumed by the negative-vanishing node. That node explicitly gives the degree bound for right derived functors. Both inputs are degree-zero sheaves (b_! is exact), hence the two objects lie in D^{>=0}. The use of the unbounded functor on D+ agrees with its bounded-below version, as specified by the item's actual pushpull convention.

Step 7 uses the derived cohomology long exact sequence and the unbounded derived isomorphism criterion. I wrote the two adjacent isomorphisms in the converse, which force all cohomology of the first vertex to vanish. Applying the isomorphism criterion to 0 -> A proves zero of A in the derived category, not just a loose statement about cohomology sheaves.

I checked B1-B10: no new statement-only node is needed; every object and coefficient category is introduced; existing statements and source tags are read; no new unsearched statement, duplicate, Mathlib leaf or spurious attachment is asserted. C1-C8: every non-elementary input is cited by node; each statement was opened and quotes are verbatim; generic tools are declared; no argument uses only a definition in place of a theorem. D1-D5: the proof actually assembles a degreewise exact sequence, a natural derived triangle, its counit identification and its image; it does not outsource the item to a renamed clause. E1-E7: hypotheses, objects and map directions were checked, and the naturality/descent and counit normalization are written out. Every step is under 2000 characters. Edge cases checked: M=0, empty W (K=B_M=0), W=V (H empty and the closed-unit target is zero), empty V, empty Z, and the zero coefficient ring. In each case the triangle and iff reduce correctly. Nilpotents on H do not create a stronger reduced-invariance premise: the localization result already permits any closed subscheme with the specified complementary open. No false statement or missing hypothesis was found.

## Unfinished work

None at the requested one-level stage-1 split. Existing dependencies remain separate DAG items; no Lean was written and no compiler, Lake or build tool was run.
