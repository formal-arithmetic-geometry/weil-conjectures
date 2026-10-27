# Stage-1 report: lem-sfb-finite-open-parts-fppf-sheaf

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-open-parts-fppf-sheaf.json`: item, statement, status split. Mathlib verdict: no match after LeanFinder (two phrasings), Loogle, LeanSearch, and source grep through the required search command. Five proof steps use existing nodes only.
- `citations.json`: twelve step/node entries, each with a verbatim quotation checked against the cited node's statement.
- `report.md`: this report. No new DAG nodes; no Mathlib leaves created. The sandbox also retains the actual `searches.jsonl` and the writing script.

## Attachments

None. Searched the live project's `lean/WeilConjectures/` for the item's blueprint tag and for finite-open-parts, finite open subschemes, finite-part sheaves, and finite_open_parts. The hits concern finite neighbourhoods, finite open covers, or unrelated finite parts of characters. No declaration states the present sheaf assertion. No sorry-bearing declaration is treated as a finished proof.

## WANTED

None. All sources used are available in the read clone.

## Findings and changes

The imported statement agrees with Stacks 04PE(1), restricted to schemes, including its lack of hypotheses on the morphism f. It required a proof, not a statement correction. The imported Mathlib searches and the full blueprint ancestry were retained; the actual Q15 search results were appended. The item is not a Mathlib leaf: the finite base-change hits, the general fpqc-to-fppf property-descent instance, and the Zariski gluing constructions returned by the second phrasing do not state descent for these pairs.

The proof follows the first paragraph of Stacks `spaces-more-groupoids.tex`, lemma-finite-sheaf, Tag 04PE. Its three operations are scheme morphism descent, descent of open subschemes after base changing the cover, and descent of finiteness. For these scheme objects, the source's algebraic-space descent inputs are specialized through the existing scheme nodes for Tags 023Q, 03N0 and 02LA. This does not add separatedness, quasi-compactness, or finite presentation assumptions on f. Step 1 also spells out the restriction maps and why they preserve finiteness.

The unit and chapter records were read, together with the newest blueprint's `sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md` (3). This is a supporting algebraic-geometric input far below the finite-open-parts construction in the recorded ancestry. This item does not realize the unit's key statement, so no unit record is edited. Whole-DAG searches by sources and key words and whole-blueprint searches (`finite open`, `03N0`, `04PE`, `finite.*open`) were read. There is no blueprint assertion to attach as `same_as`. The ancestor command returns None: the inherited null from.node and its already precise from.place/via chain are retained.

## Not duplicates

No new nodes were created. In particular, compatible open descent is already `lem-weil-pbc-open-subscheme-fpqc-descent`; the similarly named `lem-weil-pbc-etale-open-fpqc-descent` has an etale hypothesis and was not needed. Finiteness descent is already `lem-weil-pbc-fpqc-descend-finite`. Its same-unit algebraic-space version `lem-sfb-space-finite-fppf-descent` is unnecessary for scheme inputs. Representable descent and both covering lemmas are existing Mathlib leaves. No clause of the item was repackaged as a new node.

## Review by Q15

I read the statement and the first proof paragraph of 04PE in `spaces-more-groupoids.tex` with the construction of the functor just above it. For the scheme descent inputs I read `descent.tex`, lemma-fpqc-universal-effective-epimorphisms (023Q), lemma-open-fpqc-covering (03N0), and lemma-descending-property-finite (02LA). I read `topologies.tex`, lemma-fppf (021O), part (3), and lemma-zariski-etale-smooth-syntomic-fppf-fpqc (022C). For the extra restriction check I read Mathlib `AlgebraicGeometry/Morphisms/Finite.lean:60-62,88-93`, the finite base-change instances returned by the searches. I also read the FlatDescent and Representability hits: they concern descent of morphism properties and Zariski local representability, rather than the present assertion. There are no new nodes needing independent source checks.

For step 1, the statement of `def-pc-fibre-product` explicitly gives the universal property, existence, and functoriality; `def-weil-open-immersion` gives the identification with the open subscheme carrying the restricted structure sheaf; `lem-trf-finite-radicial-basechange` explicitly asserts arbitrary base-change stability of finite morphisms, independently of its additional radicial clause. The two fibre-product descriptions have the same maps into X and T, so their comparison and its inverse are obtained from the universal property. Pullback of an open subscheme is the open inverse image, with the restricted structure sheaf. This is a short construction from the cited definitions, not a hidden general descent theorem. The identity and composition conditions are equality of inverse-image operations. This step is elementary relative to the cited statements.

For step 2, `lem-trf-fppf-covering-is-fpqc` states exactly that the same covering family is fpqc. `lem-weil-pbc-fpqc-representable-descent` has arbitrary scheme targets and arbitrary fpqc covering families: apply its existence/uniqueness with target Y. I checked the extra requirement that the result is over S, rather than merely a scheme map. Applying its uniqueness with target S equates the two structure maps because all the a_i were S-maps. No subcanonical algebraic-space representability comparison is being assumed.

For step 3, `lem-trf-fppf-covering-base-change` states preservation of an fppf family under an arbitrary scheme base change, with no hypothesis on the morphism W to T. The conversion to fpqc is again precisely the existing covering node. The overlap used for the open-descent theorem is W_i times_W W_j, not an intersection of affine opens or a product over Y alone. I checked it is the same as the original matching overlap after adjoining the X projection, using the fibre-product universal property. `lem-weil-pbc-open-subscheme-fpqc-descent` supplies existence AND uniqueness of an open subscheme from equality of the two pulled-back opens; it has no etale hypothesis. The specific open-descent node is used here as a generic tool outside its unit; the reason is declared in split_report.tool_uses.

For step 4, `lem-weil-pbc-fpqc-descend-finite` is stated for an arbitrary scheme morphism and a family fpqc cover, not only a singleton surjective flat quasi-compact morphism. Its base-changed maps here are exactly Z_i to T_i, which are finite by the matching-family data. This checks all the hypotheses and supplies only finiteness of the already constructed Z to T. The comparison of the base changes uses the actual open subschemes of step 3, not abstract isomorphic local schemes needing further descent data. This is the other declared generic tool use.

For step 5, the uniqueness clauses of the scheme-map and open-subscheme descent statements are quoted verbatim and suffice: first set b=a, then compare opens in the same ambient fibre product. No new descent or equality theorem is hidden here. This is an elementary application of the two uniqueness clauses.

I tested the empty base and empty covering (the sole open in the empty fibre product and the sole map from the empty scheme give the unique pair), the empty source (only the empty finite open, reducing to morphism descent), the empty chosen opens, identity covers, and covers with repeated members. For a non-quasi-compact base, the argument still uses an fpqc FAMILY, so it never incorrectly replaces it with a quasi-compact total coproduct. For a nonseparated or non-finite-type f, each theorem still has its hypotheses: none imposes a property on f. Finite does not mean finite locally free here, so no flatness is accidentally added to Z to T. Every proof step is below 2000 characters (indeed all five together are below 3000); there is no long step hiding a comparison lemma. The statements are TeX, unsplit replacement lemmas were not created, all cited facts were read in the statements rather than their proofs, and there is no SGA citation.

## Unfinished work

None in this stage-1 split. The existing generic descent nodes remain responsible for their own proofs; this delivery supplies their correct assembly and adds no new obligations.
