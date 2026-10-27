## Worker report

Item: lem-trf-small-sheaf-coproduct-labels. Group Q44. Stage 1 only, 2026-10-22.

### Files written

- dag/nodes/sec-trace-formula/lem-trf-small-sheaf-coproduct-labels.json: existing statement, now split into seven proof steps; all clauses and statement dependencies preserved. No full Mathlib match.
- citations.json: one verbatim statement excerpt for each step/node citation (11 entries).
- searches.jsonl: the unmodified search-command log; its six actual searches have been appended to the item's pre-existing search records.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files written and no compiler, Lake or build invoked.

### Attachments

None. Searched lean/WeilConjectures for the exact item id, sheaf coproducts, and empty coverings. The existing scheme-component comparison in AlgebraicGeometry/EtaleCoproductRepresentation.lean concerns sheaves on a coproduct of schemes, not coproducts of arbitrary sheaves on a general small site. Neither it nor the module-sheaf coproduct declarations states this item.

### WANTED

None.

### Problems found and changes

The imported item had a statement and searches but no proof. Its statement is correct and remains unchanged. In particular, the empty covering is essential: the coproduct of no set sheaves need not have an empty section set on every object. The proof now treats this explicitly, rather than asserting that label-disjointness is unconditional on sections.

Used the existing family-site sheafification theorem for existence and its universal property, not the definition of sheafification alone. Used the existing local-sections theorem for both local representatives and local equality, not an implicit plus-construction claim. The coproduct universal property is verified directly on labelled pairs, so no pointwise-presheaf-colimit theorem needs a new node. Sectionwise injectivity implies categorical cancellation by evaluation, written out in step 4.

The ancestor and whole-blueprint searches were run with tools/blueprint_refs.py (sheafification, coproduct sheaves, and ancestor of this item); the source/tag and keyword search also read matching DAG nodes. The current main-20261015 update of lem-trf-local-term-locality is respected: this item is a generic auxiliary sheaf tool along its existing ancestry, not a replacement of the geometric local-term route. The chapter and unit records were read, and remain unchanged because this item is not their key statement.

The two generic off-unit tools are declared in split_report.tool_uses: lem-weil-pbc-sheafification-plus-theorem supplies set-sheafification existence/universality on a covering-family site, and lem-weil-pbc-site-sheafification-sections-local supplies local sections and local equality. These are general site tools; they do not replace any geometric step of sk-i-curve-zero. Their statements were opened and read in full. No new supporting lemma is necessary.

### Unfinished work

None in the mathematical split. Delivery validation is recorded below after the tool returns.

## Not duplicates

No new nodes are proposed. The existing sheafification-plus and local-sections nodes are reused. Their same-tag neighbours are not duplicated.

## Review by Q44

I read the source statements and arguments in literature/stacks-project/sites.tex: Theorem 00WB (theorem-plus), the universal-property discussion of Proposition 00WH (proposition-sheafification-adjoint), Lemma 00WI (lemma-colimit-sheaves), and Lemma 00WK (lemma-sections-sheafification). The tag/label correspondences were checked in literature/stacks-project/tags/tags. I also read the exact statements of every cited DAG node. There are no new nodes needing independent source checks.

Step 1 uses lem-weil-pbc-sheafification-plus-theorem, whose clauses (2) and (3) actually assert that the double plus is a sheaf and is a universal-property sheafification. Its site and set-presheaf hypotheses hold: restrictions of the labelled sum preserve labels and satisfy the functor laws. The chosen set universe contains the small site and the small family of values, so forming the labelled sets introduces no large diagram.

Step 2 uses def-weil-pbc-sheafification for its unique factorization and def-weil-pbc-category-colimit for the universal property to prove. Given f_i, the map on a pair (i,s) is explicitly f_i(s), with naturality checked through label-preserving restrictions. The inverse construction and uniqueness are stated. This elementary argument works without any inhabitedness assumption on I.

Step 3 uses lem-weil-pbc-site-sheafification-sections-local. Its statement gives precisely the covering and presheaf sections lifting a sheafification section; decoding those sections as labelled pairs adds no theorem. The same node also explicitly gives local equality, which is what steps 4 and 5 use. Step 4 additionally uses the sheaf equalizer condition of def-weil-pbc-sites-and-cohomology to pass from equality on a cover to equality of two sections of the same G_i. Cancellation of sheaf maps is then checked on every section of every object, so no unstated equivalence between monomorphisms and sectionwise injections is being invoked.

In step 5 local equality is applied to (i,s) and (j,t), not to sections of different presheaves. Equality in P(W) projects to equality of their labels, contradicting i != j for each possible cover index. This proves that the covering index set has no elements. The site definition explicitly includes closure of coverings under bijective reindexing, so replacing that index set by the empty set gives an actual empty covering family. I checked that no saturation or subcanonicality assumption is silently being used.

Step 6 uses only the equalizer definition of a set sheaf, quoted from def-weil-pbc-sites-and-cohomology. Both empty products are singletons and their equalizer is a singleton, giving existence as well as uniqueness of a section on an object with empty covering. Step 7 again uses local representatives from the local-sections node: a representative in an everywhere-empty presheaf rules out every index of the witnessing covering. Reindexing makes that covering empty; the converse singleton assertion is step 6. Thus the empty-index clause is proved in both directions.

I tested the edge cases: I empty on a site without empty covers gives no sections; I empty on an object with empty covering gives exactly one section; I a singleton recovers the original sheaf; when a site allows empty covering at every object, every sheaf has singleton values and different labels may coincide, exactly as allowed by the statement. The proof never infers i = j from equality after sheafification without first restricting to a cover. No representable-sheaf or enough-points assumption occurs.

Against delivery-errors B--E: there are no new statement-only or Mathlib nodes to check, no proof moved into a restatement of a clause, no hidden non-elementary input, no citation to a definition for sheafification existence or local equality, and no change to the item's hypotheses. citations.json quotes the cited statements verbatim. Each proof step has 326--613 characters, so none triggers the long-step review threshold. The Mathlib queries were executed only through msearch.py; all six services/calls succeeded. Read the hits in Sites/Limits.lean:189--219, LocallyInjective.lean:163--193, LocallySurjective.lean:291--306, Sheaf.lean:467--473 and LeftExact.lean:319--330. They cover portions of the item but not every clause by one-line specialization. I retained the earlier searches rather than rewriting their history.
