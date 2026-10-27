## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-unramified-etale-compatible-charts.json: item split, statement unchanged, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-unramified-etale-locality.json: one new statement-only node, unsplit, no Mathlib match.
- citations.json: one verbatim statement quotation for every step/cited-node pair.

## Attachments

None. Searches of lean/WeilConjectures/ by the blueprint tag, compatible charts, algebraic spaces, and unramified locality found no declaration stating the whole item. Scheme-only declarations are not attachments to this algebraic-space item.

## WANTED

None. All mathematical sources used are available locally.

## Issues and unfinished work

The item had no proof. Its source references are correct, but the existing scheme etale source-and-target locality node lists five properties and unramifiedness is not among them. I did not assume that it covered unramifiedness: the single new node supplies precisely that scheme input. The general presentation criterion already exists and is cited rather than duplicated. The existing algebraic-space unramified permanence node depends on this item and is deliberately not used in its proof.

The blueprint ancestor tool returns null for this existing created-node chain; I retained the existing ancestry and prepended the item in the new node's via list. I read the latest sk-thm-sf-ctf-stability section and direct-images proof. This auxiliary chart calculation does not replace a unit step or change a chapter route. No Lean, compiler, or local validation tool was run. The remaining proof of the new scheme-locality node is future stage-1 work, as required for new nodes in a one-level split.

## Review by Q61

I read spaces-morphisms.tex Tag 03MJ, lemma-local-source-target, including its common-refinement proof, Tag 03ZH, definition-unramified, and Tag 03XT, lemma-etale-local, clauses (7)--(8). These agree with the item's quantification over compatible diagrams: only the source vertical map must be surjective for recognition. The target vertical map need not be surjective in that equivalence. I also read spaces.tex Tag 02X1, lemma-lift-morphism-presentations: it constructs the source scheme by pulling a prescribed target atlas back to an independently chosen source atlas. That is why the second step proves the stronger prescribed-target assertion instead of citing the existential clause of 03MJ as if it included a prescribed atlas.

For the new node I read descent.tex Tag 04QZ, definition-local-source-target, and Tag 04R3, remark-list-local-source-target, item (9). I checked the references to Tag 03YV, lemma-unramified-etale-local-source, and Tag 02VM, lemma-descending-property-unramified; the former uses differential descent, not merely the definition of unramifiedness. The new statement writes all three clauses of 04QZ explicitly and introduces every scheme, point and map. It requires no finite-presentation hypothesis on the morphism being tested. It has no proof sketch or proof dependencies. Its four notion dependencies actually define schemes, unramifiedness, etaleness and scheme fibre products.

Step 1 uses the new node for unramified scheme locality and the existing lem-sfb-scheme-etale-source-target-properties for etale scheme locality. I opened both statements and matched their three locality clauses with the explicit hypothesis of lem-sfb-space-etale-presentation-property-criterion. The latter's statement gives the equivalence of the universal chart condition and one diagram with surjective source, and explicitly does not require a surjective target chart. Thus this is a specialization of an existing general theorem with its missing hypothesis supplied, not the item's clauses renamed as new nodes. The two cited definition nodes give the isomorphism-invariant scheme notions. No argument from a cited proof is taken as part of its statement.

Step 2 uses def-trf-algebraic-space for the initial source atlas and the meaning of representable surjective etale maps. The actual statement of lem-trf-space-fibre-products-etale-covers gives both the representable scheme pullback when one factor is etale and the stability of a jointly surjective etale family under base change; I use it for singleton families. I verify the composite atlas on each scheme T over X, where both arrows are scheme morphisms. Only there do I apply lem-weil-pbc-etale-composition-cancellation, clause (2), and lem-trf-surjective-morphism-composition. The latter is a scheme lemma, not a theorem about general algebraic spaces. The associativity identification is written out in terms of the same triples of sections, so it is a finite-limit identity and hides no descent or representability lemma. All needed representability follows before scheme composition is used. Neither atlas is assumed quasi-compact. The target atlas is fixed before W is chosen, and the construction satisfies the requested commutative equation.

Step 3 checks the empty cases from the definitions. If X is empty then U is empty for every compatible diagram; the scheme properties on its empty source are vacuous. If Y is empty then a morphism X to Y forces X empty. For the new locality statement with X empty, its pointwise right side is vacuous and the left side also holds; with the identity chart over a nonempty scheme the usual scheme notion is recovered. Nonseparated schemes and arbitrary non-Noetherian bases do not enter any forbidden affine-intersection or finiteness argument. A non-surjective source chart would fail to see an unramifiedness defect on another component; this confirms the significance of the surjectivity retained in the statement. A non-surjective target chart is harmless when the source chart is surjective, exactly as the criterion states.

I read each Mathlib search's hits, using a second wording for both the item and the new node. The item searches return schemes, not algebraic spaces. For the new node, the relevant hits are FormallyUnramified.of_comp and its base-change and composition instances, IsEtale.of_comp, and the ring-map localization results. I read Morphisms/FormallyUnramified.lean, Etale.lean, and LocalFlatDescent.lean; the latter descends properties through a surjective flat quasi-compact TARGET base change, not arbitrary etale SOURCE charts. Combining those results would require an argument, so this is not a one-line Mathlib specialization. Search queries in mathlib_searches are exactly the logged calls, with result summaries rather than invented declarations. I did not record a down service as no match.

I checked delivery-errors B--E against the actual statements and source text. The new node is strictly a scheme-locality prerequisite, not an algebraic-space recognition clause; there is no restatement of the entire item. The existing general criterion is reused. No new statement is disputed, and no statement correction is made. Each step is below 2000 characters (873, 1178, 567), so none has a concealed long subargument. I corrected the potential C4 error of applying the five-property locality lemma to unramifiedness by creating the missing input. I also avoided applying a scheme surjectivity composition lemma directly to space morphisms by writing the scheme tests. Generic off-unit tools are declared in split_report.tool_uses. Citations contain literal complete statement strings, hence each requested quote is an actual part of the cited statement.

## Not duplicates

The following comparisons cover every existing node found by the new source's tags (04QZ, 04R3, 03YV, 02VM, 04R2), also searching whole-node references rather than only source fields. Whole-DAG keyword searches and blueprint_refs searches for unramified, unramified etale, 03YV, 04R3, 04R1, local source target, and presentation found no existing unramified scheme-locality statement.

lem-sfb-scheme-unramified-etale-locality vs lem-sfb-scheme-etale-source-target-properties: the existing list has smooth, etale, flat, locally finite presentation and locally finite type; it omits unramifiedness.

lem-sfb-scheme-unramified-etale-locality vs lem-sfb-space-etale-presentation-property-criterion: the existing theorem assumes scheme source-and-target locality for a general property; the new node proves that hypothesis for unramifiedness.

lem-sfb-scheme-unramified-etale-locality vs lem-sfb-unramified-etale-compatible-charts: the item recognizes algebraic-space properties and constructs prescribed compatible atlases; the new node only asserts locality on schemes.

lem-sfb-scheme-unramified-etale-locality vs lem-sfb-space-unramified-permanence: the existing node proves space composition, cancellation and base change, not scheme source-and-target locality; it depends on the item, so cannot be a substitute here.

lem-sfb-scheme-unramified-etale-locality vs lem-sfb-stack-chartwise-smooth-etale-calculus: the existing stack list omits unramifiedness and concerns representable stack morphisms, not the missing scheme-locality hypothesis.

lem-sfb-scheme-unramified-etale-locality vs lem-galois-fpqc-descend-unramified: the existing node descends unramifiedness along target fpqc covers; it does not give source etale locality or the three source-and-target clauses.

lem-sfb-scheme-unramified-etale-locality vs lem-galois-fpqc-descend-etale: the existing node concerns etaleness under target fpqc covers, not unramifiedness under source-and-target charts.

lem-sfb-scheme-unramified-etale-locality vs lem-galois-fpqc-descend-open-immersion: the existing node concerns target descent of open immersions, not locality of unramifiedness.

lem-sfb-scheme-unramified-etale-locality vs lem-galois-fpqc-family-descent-of-local-property: this generic fpqc TARGET descent theorem assumes the descent property and does not supply SOURCE locality for unramifiedness.

lem-sfb-scheme-unramified-etale-locality vs lem-galois-lft-formally-unramified-single-fpqc-descent: its two descent assertions require a surjective flat quasi-compact target base change; there is no arbitrary etale source locality or compatible-square criterion.

lem-sfb-scheme-unramified-etale-locality vs lem-trf-geometric-fibre-unramified-criterion: this tests a locally finite type map on geometric fibres, not on etale source-and-target diagrams.

lem-sfb-scheme-unramified-etale-locality vs lem-sc-etale-local-ring-faithfully-flat-descent: this tests etaleness of a finitely presented algebra after field extension at a prime; it is not unramified scheme chart locality.

lem-sfb-scheme-unramified-etale-locality vs lem-sc-etale-base-change-geometric: this tests etaleness after extension of the base field at corresponding points; it does not give the unramified source locality statement.

lem-sfb-scheme-unramified-etale-locality vs lem-sfb-stack-representable-unramified-descent: this descends a representable stack morphism along a flat locally finitely presented TARGET cover; it does not give arbitrary scheme SOURCE charts.

## Validation

The server review_split check passed. Full dry-run and delivery results are recorded by the delivery tool.
