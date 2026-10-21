# Worker report: lem-sp-chart-counit-scalar-transport

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-chart-counit-scalar-transport.json`: statement, split; no Mathlib match. The statement and original metadata are retained. Seven proof steps now establish both equations and the refinement assertion.
- `citations.json`: twelve entries, one for every dependency cited by every proof step; quotes copied verbatim from the current dependency statements.
- `searches.jsonl`: the five actual Mathlib searches made through the required search command. Existing searches in the item were retained.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. No unit record needs editing: this item is a lemma below the unit's key statement.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for chart/counit/scalar combinations found no declaration stating the item. The general scalar-extension counits and derived adjunction/coherence declarations found there do not assert the chart scalar equation with both sites and the specified compact-support comparisons. The purity-preservation file concerns bounds for exceptional pullback, not these coefficient identities.

## WANTED

None.

## Corrections and route

No statement correction or statement dispute. The unsplit item had no argument. Its seeded dependencies introduce the functors and comparisons but do not alone supply the two geometric input counit equations. The proof now cites the existing affine scalar-counit, etale-sum scalar-counit, fixed-left normalization, and finite-Tor chart-domain nodes as well. It does not create a duplicate or shift a clause into another node.

Read the current blueprint's unit `sk-lem-sp-reduction/_section.md` and `sk-lem-sp-reduction-exceptional.proof.md`, especially Charts. The unit's route is retained: sum evaluation followed by ordered affine integration, fixed left normalization, and etale/pro-etale transport. The P1/Kummer/diagonal calculations are already the inputs of the existing affine-counit node; this split does not substitute a different purity route.

One generic tool from another unit is `lem-sp-et-proet-coefficient-compatibility`: its coefficient/site and refinement squares identify the actual named maps used here. This is declared in `split_report.tool_uses`. The chart unit supplies the adjunction, not those compact-support coherence squares. The other declared generic tool is `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, whose statement computes the derived pullback/tensor comparison on flat-term K-flat representatives; Step 1 uses exactly that description to identify the two canonical tensor maps.

Mathlib searches used two semantic phrasings, Loogle, grep and LeanSearch. The Loogle hit `CategoryTheory.Adjunction.comp_counit_app` was read at Mathlib/CategoryTheory/Adjunction/Basic.lean:580 (with the composite-adjunction definition at 567). It only expands a composite counit; the item also requires geometric coefficient identities and fixed-map normalization. LeanFinder returned affine-space and standard-etale descriptions for the first query, and general counit formulas/condensed equivalences for the second. LeanSearch returned ordinary ring/module scalar constructions; grep had no hits. None states the item. No search service was unavailable. The categorical expansion is used directly as a definition calculation, not promoted to a new node.

## Not duplicates

No new nodes. Whole-DAG searches for this item and the chart/sum-then-affine counit, and whole-blueprint searches for scalar counit, chart counit, coefficient comparison and summation, located the existing inputs and the ancestor `det-sp-reduction-exceptional`. The ancestor proves a different assertion, invertibility of the exceptional comparison, and uses this lemma. `sk-lem-sp-finite-existence` describes a chart adjunction, not compatibility with changing coefficients. Therefore `blueprint.same_as` remains empty; the existing precise `from.place` is retained.

## Review by NS

I read the item against the current Charts paragraph and the unit's second step, then opened the statement of every cited node. This is a proof of the specified chart counits, rather than merely an assertion that some adjunction comparison exists. I also read Stacks `more-etale.tex`, label `lemma-shriek-composition` (0F7J), including the construction and the start of choice-independence through common compactifications, and label `remark-Rf-lower-shriek-change-of-rings` (0GL6). They support the construction route, but neither is being cited as if it independently stated the site/coefficient square: that square is explicitly in the existing compatibility node. The proof origin is agent, since the blueprint sketch and this pasting calculation are agent-written. There are no new nodes needing separate sources.

Step 1 uses the chart-adjunction statement for its composite right functor and its sum-then-affine counit, and the chart-domain statement for bounded constructible finite-Tor domains, preservation by the needed pullbacks/twists/shifts and scalar extension, and intertwining through site comparison. The general ringed-topos tensor/pullback statement supplies the K-flat computation used in this identification. The canonical right coefficient map factors as the pullback scalar map followed by pullback of the affine scalar map: its representative tensor and Tate images are written out. No arbitrary orientation of the Tate line is chosen.

Step 2 uses exactly the displayed scalar-counit formula in the affine node and exactly the displayed sum/evaluation formula in the etale-sum node. The affine base is Y; the etale target is V and its input is G_A K, which Step 1 puts in the required category. All schemes are separated finite type over the same field, e is separated etale finite type, ell differs from the characteristic, and the common ell-power annihilator meets each input's hypotheses.

Step 3 is elementary algebra of the two equations from Step 2: first expand the composite counit, move a_d past the sum counit by naturality, substitute its scalar equation, move T(v_A) past beta_d by naturality, then substitute the affine equation. All objects and the map at which naturality is used are specified. It invokes no additional black box.

Step 4 uses the precise statement of the fixed-left scalar-normalization node, which supplies BOTH the coefficient square with the named beta_g and preservation of the sum-then-affine counit. Precomposing by T(lambda_A) displays a common invertible factor. The cancellation proves the identity for the actual fixed compactification and not just an endpoint isomorphism.

Step 5 uses the transported-counit formula in the chart-adjunction node, the full displayed coefficient/site square in the compatibility node, and the chart-domain statement's intertwining of scalar, inverse-image, Tate and shift comparisons. All square directions are checked: F_B(delta_U) b is obtained by right multiplying the square by T(c_A) inverse. The canonical right map after H_B(delta_Y) is C_U(a_et) delta_U.

Step 6 is the explicit elementary substitution from Step 5. Naturality of the B-counit inserts H_B(delta_Y); naturality of c_B inverse moves C_U(a_et) to C_Y F_et(a_et). The middle c_B inverse/c_B cancel, Step 4 applies, and naturality of delta_Y identifies the result with delta_Y T(epsilon_tilde_A). Cancellation of delta_Y yields the claimed named b_g equation. Thus the word transport does not hide an extra lemma.

Step 7 uses the comparison equivalence stated in the chart-adjunction node, so every pro-etale input is covered by the calculation on comparison objects. Naturality at a comparison isomorphism proves the extension to all inputs. The compatibility node states the exact refinement square for both beta and b and for common refinements; the left-normalization node states that its counit identification holds for every chosen compactification through these canonical comparisons. The proof writes the refinement counit as epsilon phi(H) inverse and cancels the displayed refinement square. This checks the final clause without changing the left map.

I checked the B--E checklist: no new unsupported, duplicated or elementary nodes; no hidden non-elementary claims used only by tag; no use of another node's proof instead of its statement; no clause merely relabelled; no circular appeal to the ancestor or to exceptional coefficient invertibility. The server dry run will check DAG acyclicity and route mechanically. Every step is below 2000 characters. All citation quotes were checked as literal substrings of the corresponding statements.

Small cases: d=0 reduces to the sum counit because the affine adjunction is the identity; e=id reduces to the affine equation; an empty etale fibre makes the sum map zero on both paths; A=B with identity map makes each scalar comparison the identity; a nonflat map Z/ell^2 to Z/ell is permitted because all tensor operations are derived and each cited input explicitly allows arbitrary finite coefficient maps. Even shift 2d introduces no sign. The N=1 case permits only zero coefficient rings and gives the zero-category identities. No extra flatness or finite-projective-dimension hypothesis has entered.

## Unfinished work

None in this one-level split. Its non-elementary inputs are the existing DAG nodes, to be handled under their own items. No Lean file was written or compiled, no repository or launcher file was modified, and no agent was started.
