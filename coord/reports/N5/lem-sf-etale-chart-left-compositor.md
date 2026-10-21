# Stage-1 report: lem-sf-etale-chart-left-compositor

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sf-etale-chart-left-compositor.json`: statement, split into six proof steps; not a Mathlib leaf. The statement and statement dependencies are unchanged.
- `citations.json`: eleven step/node entries, each quoting a verbatim substring of the cited node's statement.
- `report.md`: this report. `searches.jsonl` was produced by the required search command.

New nodes: 0. New Mathlib leaves: 0. No unit record needs changing: this item is a subsidiary node, not its unit's key statement.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id and for chart comparisons, factorizations, immersion normalizations and compact-support comparisons. I read the relevant source in `SixFunctors/Etale/Derived/LowerShriek.lean`, `LowerShriekComposition.lean` and `LowerShriekFormalismComparison.lean`. They provide ingredients, including the canonical bounded-below compositor; they do not state the whole normalized six-factor chart comparison with its specified component formula. The general unbounded nonempty composition isomorphism in LowerShriekComposition does not specify this normalized transformation and cannot attach this item.

## WANTED

None. All sources used are present locally.

## Problems found and repaired

The imported item was statement-only. I found no statement error, no missing hypothesis and no need to weaken or change its formula. I supplied the argument rather than moving its assertion to another node. In particular the bounded-below intermediate-domain assertion now has an explicit resolution proof, not an implicit appeal to the existence of the compositors. The equality of scheme morphisms is used by equality transport, not by choosing an arbitrary isomorphism of compact-support functors. The final comparison is defined by its actual components; naturality and compatibility with canonical compactification changes are proved by equations of morphisms.

## Unfinished work

None for the one-level split. The existing normalization node is unsplit and remains a cited dependency; this delivery does not attempt to prove or alter it. Existing nodes' proofs and Lean metadata were not edited.

## Searches and reuse

The sandbox initially had no item node, no report and no earlier search log. I retained the repository item's five original search records and appended the five searches actually run through `batch2/msearch.py` for this item: two LeanFinder phrasings, Loogle, source grep in Mathlib/CategoryTheory, and LeanSearch. All services answered. I read all returned signatures. The hits concern equality congruences for underived module pushforwards, Zariski restrictions, or general exact/derived-functor comparisons; they do not state the normalized ordinary-etale compact-support chart comparison. No search was invented or recorded as unavailable when it answered.

Whole-DAG tag/keyword searches included 0F7J, 0F7K, equal factored chart and the item's title. Whole-blueprint searches through `tools/blueprint_refs.py search` used `compact support`, `factored chart`, `chart comparison`, and `immersion normalization`. The blueprint ancestor command returns `sk-prop-sf-rf-shriek-preservation`. I retained the precise opening/final-paragraph provenance and its via list. No blueprint node states this full normalized chart comparison in another form, so `same_as` is empty.

## Not duplicates

No new node was created. In particular, compactification independence and composition are reused from `lem-amb-etale-compact-comparisons`, and immersion exactness and normalizations from `lem-sf-etale-immersion-shriek-normalization`. They are ingredients, not duplicate replacements for the item. The parent `lem-sf-etale-chart-adjoint-comparison` asserts Hom bijections involving right adjoints and depends on the present source comparison; it is neither used here nor duplicated.

## Tool uses

`lem-amb-etale-compact-comparisons` is the generic compact-support compositor and canonical-change tool. `lem-weil-pbc-module-sheaves-enough-injectives` and `lem-weil-pbc-dplus-injective-representative` are generic homological tools for checking boundedness. Their use does not replace the closed/projection and open-locality route of the unit. They are declared in `split_report.tool_uses`; no maintainer-owned top-level tool_uses field was changed. The compact-support definition is a notion, and the immersion-normalization node is in the item's own unit.

## Review by N5

I read the chapter and unit records, the current main-20261015 unit statement and `sk-prop-sf-rf-shriek-preservation.proof.md` (opening factorization paragraph and final paragraph about composition with source/target open restrictions). For the item I read Stacks more-etale.tex Tag 0F7I (`lemma-shriek-well-defined`), Tag 0F7J (`lemma-shriek-composition`, including the choice-independence diagram), and Tag 0F7K (`lemma-pseudo-functor`, the statement and setup). These supply precisely the canonical composition and compactification-choice comparisons already stated by the reused comparison node. I also read the current blueprint proof of `lem-amb-etale-compact-comparisons`; the delivery uses that node's statement, not its internal proof. No SGA source is used. There are no new nodes whose sources require separate review.

For step 1 I opened the complete statements of the three cited nodes. The module-sheaf enough-injectives node explicitly covers constant coefficients on any small etale site; the representative node explicitly gives injective representatives with the SAME lower bound and says bounded-below injective complexes are K-injective; the compact-support definition explicitly gives termwise open extension and total direct-image computation on K-injective representatives. I read their source ingredients: injectives.tex Tag 01DU (`theorem-sheaves-modules-injectives`), derived.tex Tag 013K (`lemma-injective-resolutions-exist`, parts 2 and 3), and Tag 070J (`lemma-bounded-below-injectives-K-injective`). The two representative choices in step 1 have the relevant enough-injectives hypothesis. Degreewise j_! and r_* send the zero sheaf to zero, so the resulting complex has the same strict lower bound. This proves the required compact-support preservation directly in the ambient unbounded category, independently of a finite cohomological-dimension assumption.

For steps 2 and 3 I opened the complete normalization and compositor statements. The former explicitly says the exact immersion functors preserve every lower bound and gives n_s and n_v in the direction Rj_! to Dj_!, and n_i in the direction Ri_! to Di_*. The latter explicitly gives alpha_(b,a): Rb_! Ra_! to R(ba)_!, naturally on bounded-below inputs. I additionally read the normalization source facts: more-etale Tag 0F51 (`lemma-proper-f-shriek`), etale-cohomology Tag 04FX (`lemma-stalk-pushforward-closed-immersion`) and Tag 03S5 (`proposition-describe-jshriek`). I verified every intermediate type of the six arrows. In particular alpha_(v,pi) is inverted AFTER substituting fs=vpi; alpha_(p,i) is inverted inside Rv_!; n_i is then mapped through both Rp_! and Rv_!; and n_v is evaluated at Rp_!Di_*H. The source and codomain of each neighboring arrow agree. The hypotheses supply Noetherian schemes and compactifiable separated finite-type maps for every compositor, including pi. Step 1 and the exact immersion preservation clause check every bounded-below input. Finite A is the same constant ordinary-etale module coefficient ring in both cited nodes; no pro-etale comparison or invertibility assumption is introduced.

Step 4 uses no additional theorem: a functor maps an inverse pair to an inverse pair, and cancellation in the reversed finite chain proves invertibility. I wrote those identities rather than declaring the full desired comparison to be a new lemma.

For step 5 the two cited statements say exactly that their maps are natural. I checked inversion by multiplying a naturality square by inverse components, and whiskering by applying the outer functor. The t_j calculation then moves F_0(a) past the six factors in order. This yields the equation in the item, in its stated direction, and makes the components an actual natural transformation on the full bounded-below subcategory. This is an elementary finite composition calculation from the cited naturality equations, not an uncited sheaf or compact-support theorem.

For step 6 I checked the explicit choice clauses in both cited statements: the compositor is independent of compactification choices and the specified immersion normalizations commute with canonical compactification changes. Their whiskered squares give c_j t_j = t'_j c_(j-1); if the outer functor changes, its comparison is natural at the inner arrow. Multiplying these equations gives c_6 gamma = gamma' c_0. The endpoints are exactly the changes of Rf_!Ds_! and Dv_!Rp_!Di_*. The existing cocycle clause covers successive changes. No assertion about arbitrary unbounded inputs, right adjoints or Hom comparisons is used.

I checked delivery-errors B through E against the files and sources. No statement-only auxiliary hides a proof, no new elementary/duplicate/restatement node is introduced, each substantive input is a cited statement, and citations.json quotes those statements verbatim. No dependency points back to the parent. The Mathlib searches are logged as run. The six proof texts have 1149, 934, 812, 406, 989 and 1417 characters, all below the long-step threshold; the only self-contained homological subargument reuses the existing resolution nodes. Small-case checks include the zero object and empty source, identity immersion factors (where no arrow has an ill-typed inverse), and sheaves shifted to any positive or negative lower bound m. The resolution proof and exact immersion bounds apply uniformly to all these cases. The morphism p need not be proper, since the formula consistently uses Rp_!, not Rp_*. I did not alter the statement, definitions, unit route, chapter, repository, launcher or Lean source, and ran no compiler or Lake tool.
