# Q117: lem-trf-fppf-local-representations-fully-faithful

## Files written

- dag/nodes/sec-trace-formula/lem-trf-fppf-local-representations-fully-faithful.json: statement item, now split into six explicit steps; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for every step/node citation.
- searches.jsonl: searches actually run through msearch.py, retained without alteration.

No new nodes, Mathlib leaves, unit changes, Lean files or repository writes. The sandbox was empty of a prior item or report on resumption, and no Q117 delivery process was running. There was no saved delivery mutation to repeat.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint id and fppf/representation terminology found no declaration stating all clauses. Picard fppf representability statements and the singleton-cover sheaf condition do not give the specified functor, slice correspondences and full faithfulness.

## WANTED

None. All sources used are already in literature/.

## Source and changes

Read descent.tex, Tag 02W5 (lemma-descent-data-sheaves), including its right-to-left construction and remark-what-product-means. Read sites.tex, Tag 04TQ (lemma-glue-maps), including its proof. Verified tag/label associations in stacks-project/tags/tags. The statement is unchanged and true. The source's omitted checks are now the coordinate arguments in steps 1–4 and 6, with step 5 using the existing sheaf-morphism gluing theorem. Because these checks are supplied here rather than copied from a complete published proof, proof_origin.by is agent. No SGA source is used.

The imported parent was already reviewed; it is not used in this proof, which would be circular. The current blueprint ancestry and the unit/chapter records were read. This task supplies the generic representability support below the unit, and changes neither the unit's route nor its realized fields (it is not the key node). The existing blueprint.from.place already names exactly the forward construction and the old parent steps 3, 4 and 8.

## Searches and reuse

Searched the whole DAG by 02W5, 04TQ, Yoneda, fully faithful, local representation and gluing terminology, and used blueprint_refs.py ancestor and searches for Yoneda, glue maps and representable. Blueprint lem-pc-yoneda and lem-pc-representable-unique are related generic Mathlib results; neither is this item. The sharper existing lem-galois-yoneda-fully-faithful directly supplies the map bijection needed throughout. The set-valued morphism clause of lem-pe-set-sheaf-cover-descent is reused instead of creating a 04TQ node. The module-valued lem-pur-sheaf-hom-cover-gluing would not apply to these set sheaves.

Ran LeanSearch, Loogle, LeanFinder, and two grep searches through the prescribed msearch.py command, with different phrasings. All five searches were available. Read Mathlib CategoryTheory/Sites/Descent/DescentData.lean lines 550–628 and AlgebraicGeometry/Sites/Representability.lean lines 19–100. fullyFaithfulToDescentData is conditional on a supplied prestack and concerns its restriction functor; it does not provide the chosen scheme representatives, product/slice conversion and coordinate-preserving comparison functor required here. Scheme.LocalRepresentability is for relatively representable Zariski open immersions. Neither turns the whole item into a one-line specialization. The item's earlier search records are retained, and the five new records reproduce the new log entries exactly.

## Not duplicates

No new nodes. The existing parent equivalence and sibling inverse-gluing task are strictly larger/different constructions; neither is used as a substitute for the forward proof. No clause has been relabelled as a new node.

## Review by Q117

I checked B through E against the JSON and the sources, rather than treating successful mechanical checks as a mathematical review. The six proof steps are each shorter than 2000 characters. They carry the construction itself and introduce no hidden auxiliary lemma with separate hypotheses. The only elementary step is step 4: substitution in the explicitly constructed slice bijections and the defining descent-morphism square. It does not assume gluing or full faithfulness.

Step 1 uses the actual statement of lem-galois-yoneda-fully-faithful with the category of schemes over T: the projection of alpha uniquely gives p, and evaluating on a test map gives p composed with that map. I checked both inverse formulas for the fibre/disjoint-union correspondence and naturality under W' to W. def-pur-localized-ringed-site explicitly says that the slice restriction has value H(W), so it justifies exactly that identification, with no unmentioned inverse-image theorem.

Step 2 uses the universal mapping bijection stated in def-pc-fibre-product, not just existence of the product. The two representations of triples therefore follow on every test scheme. The Yoneda map bijection gives the isomorphism and detects equality; its inverse is obtained from the inverse natural bijection. Keeping both base coordinates proves that the map is over T_i times T_j. On triple overlaps both maps preserve the same four coordinates, so equality gives the cocycle, including repeated indices. The scheme-descent definition states the required cocycle, objects and compatible morphisms. No effective scheme descent, quasi-compactness or separation is assumed.

Step 3 again uses that exact Yoneda bijection to define f_i. The equation preserving the first coordinate proves it is over T_i. On overlaps the common formula replaces s by v(s) and fixes both base coordinates, proving the descent square. Identity and composition follow from the same concrete transformation and Yoneda injectivity, so this is an actual functor.

Step 4 cites only the descent and localization definitions, whose statements I opened. Given a compatible family of scheme maps, the displayed formula gives slice sheaf maps. On a test object of a double slice the descent square has the two precisely stated K(W) coordinates; their equality is the necessary overlap agreement. This uses previously proved coordinate identities, not a claim about a node's unquoted proof.

Step 5 uses only the morphism clause of lem-pe-set-sheaf-cover-descent: its statement explicitly grants unique gluing of maps between existing sheaves when their restrictions agree. I checked its small-site, fibre-product, universe and covering hypotheses: these are provided by the item's explicit skeleton/universe convention and the fppf cover. The site over T is its localization at the terminal object; no enlargement of the index category is used. The lemma is a generic tool from another unit, declared in split_report.tool_uses. Step 4 verifies its overlap hypothesis. The formula on every fibre then identifies R(v) with the given f via Yoneda. Conversely equality of scheme maps gives equality on every slice, and uniqueness of gluing gives equality globally. This proves both surjectivity and injectivity of the requested Hom map.

Step 6 uses the same Yoneda bijection in each over-category to turn local slice isomorphisms into local scheme isomorphisms. The already proved formulas identify overlap agreement with the descent square. The inverse squares commute too; full faithfulness then reconstructs inverse global maps, and detects the inverse identities. For naturality, the two global composites have identical local restrictions, and uniqueness proves the square. Thus the final assertions need no separate local-isomorphism detection theorem.

I checked the identity singleton cover, repeated indices, and the empty cover of the empty scheme. In the last case the sheaf axiom on the empty cover makes each section set over the sole empty test scheme a singleton, so there is exactly one map, matching the unique empty descent morphism. Empty local schemes cause no problem: their coordinate sets and bijections retain their ordinary empty-set meaning. No argument assumes sections exist. General non-affine and non-separated schemes are covered since only fibre-product universal properties, Yoneda and sheaf-map gluing enter.

Citations.json contains actual verbatim statements, not reconstructed paraphrases. Every non-elementary fact is supplied by an existing cited statement; all proof dependencies are exactly the union of uses. There is no parent/sibling citation, no cycle introduced by the construction, no new statement-only node to audit, and no statement change or dispute. Nothing mathematical remains unfinished.
