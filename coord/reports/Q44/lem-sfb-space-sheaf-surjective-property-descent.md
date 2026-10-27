# Stage-1 report: lem-sfb-space-sheaf-surjective-property-descent

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-sheaf-surjective-property-descent.json`: item, statement unchanged, split in three steps following Stacks 06NR.
- `dag/nodes/sec-six-functors-basics/lem-sfb-scheme-fppf-refinement-property-descent.json`: new statement-only lemma, Stacks 06NB; unsplit, no Mathlib match.
- `citations.json`: one verbatim statement quotation for each node used by each item step.
- `searches.jsonl`: actual launcher search log; `report.md`: this report.

## Attachments

None. The project source has no declaration with the item's blueprint tag, nor a declaration found by the sheaf-surjectivity / fppf-refinement / composite-descent searches that states all three conclusions. Related source declarations about refinements and flat source descent have different conclusions or additional flatness assumptions. No Lean file was changed or compiled.

## WANTED

None. All sources used are available locally.

## Problems and corrections

The imported item is correct as written and agrees with Stacks `spaces-descent.tex`, Tag 06NR, `lemma-curiosity`. Its empty proof is replaced by an explicit chart reduction and a compatible lifting-cover construction. No hypothesis on u was added. The scheme lemma required for the last step was absent from the DAG: Tag 06NB, `descent.tex`, `lemma-curiosity`. I reuse the existing chart-test, representable-etale, fibre-product and fppf-covering nodes instead of making new copies.

The source's shorthand refinement using V_i times_X U must retain the given map to V. I use the paired lift V_i to A = X times_Y V and the pullback D_i = V_i times_A U; the equality in A proves that its two maps to V agree. This also avoids treating an arbitrary map between spaces as a representable morphism. This is an explicit compatibility repair of the proof, not a statement dispute.

For example, the literal two projections of V_i times_X U to V need not agree even under the lemma's hypotheses: take X = Y = Z = Spec(k), V = U = Spec(k) disjoint-union Spec(k), and V_i = V with its identity covering and the unique lift to X. Then V_i times_X U has two independent component coordinates, whereas V_i times_A U with A = V enforces equality of their V coordinates. The refined product used in the delivery resolves this.

The current blueprint was read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, especially `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md` (frontmatter id `det-thm-sf-ctf-stability-direct-images`). Its current direct-image argument is a compactification argument; this generic algebraic-space descent lemma is a supporting input of the inherited geometric chain and changes none of that unit route. The ancestor tool prints `None` for this item's existing chain. I retain its null ancestor and the complete inherited via chain, and extend the precise place description for the new scheme input. Neither the chapter nor unit record is changed; the item is not the unit's key node.

## What remains

The new scheme lemma is intentionally statement-only and awaits its own stage-1 split. It is a genuine smaller scheme-theoretic input: its source has an affine-ring reduction and separate tensor-exactness / finite-generation / finite-relations arguments. The current item proves the nontrivial passage from arbitrary algebraic spaces and sheaf-local lifts to this scheme hypothesis. No proof work required for the item's one-level split is omitted.

## Not duplicates

lem-sfb-scheme-fppf-refinement-property-descent vs lem-sfb-space-sheaf-surjective-property-descent: the new node has three schemes and an actual fppf covering of Y factoring through X; the item concerns arbitrary algebraic spaces and must construct the compatible scheme covering through nested charts. It is the separate scheme input 06NB used by the source proof of 06NR, not a new name for one of its three clauses.

lem-sfb-scheme-fppf-refinement-property-descent vs lem-sfb-space-local-properties-chart-test: the latter compares a property with its values on compatible etale charts; it does not descend a property from a composite through an arbitrary arrow admitting fppf lifts.

lem-sfb-scheme-fppf-refinement-property-descent vs lem-sfb-space-fppf-covering-calculus: the latter proves stability and composition of covering families, not descent of a composite morphism's property.

No existing node has Tag 06NB or `descent-lemma-curiosity`. Searches of the entire DAG by that tag and label, by fppf refinements and the three morphism-property words, and blueprint_refs searches for `06NB`, `curiosity`, `surjective sheaf`, `algebraic space`, and `fppf covering` found no equivalent blueprint theorem. The hits on the last query are site/covering definitions, a Zariski-to-fppf lemma, and a Picard-functor sheaf statement, none of which gives scheme composite descent.

## Mathlib searches and candidates

All new search records are copied from this item's actual `searches.jsonl`, with the exact query texts. Both natural-language services, Loogle and grep were used, with second phrasings. None of the services was down. I read the returned hits and the candidate sources `Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`, `Descent.lean`, `FinitePresentation.lean`, `Flat.lean` and `Sites/Representability.lean`.

The DescendsAlong instances in FlatDescent prove base-change descent with a flat covering map; they do not cancel an arbitrary arrow admitting local lifts. The tempting `AlgebraicGeometry.locallyOfFiniteType_of_comp` cancels the other factor: it concludes a property of X to Y, not Y to Z. Composition and base-change instances do not state the required cancellation. The sheaf-surjectivity hits in Representability are gluing assertions. Hence neither the item nor the new scheme lemma is a one-line specialization of the results found. The narrow Flat.lean grep hit at line 314 is injectivity of a ring-map composite inside a proof, not a scheme-descent theorem; its single-file result formatter prints the line as its file field, and is preserved exactly in the logged result.

## Review by Q44

I read Tag 06NR (`spaces-descent.tex`, `lemma-curiosity`) for the item and Tag 06NB (`descent.tex`, `lemma-curiosity`, including the full affine reduction and all three cases) for the new node. I also read the compatible etale chart statement at `spaces-morphisms.tex`, `lemma-local-source-target` (03MJ), its flat / finite-type / finite-presentation definition clauses (03ML / 03XF / 03XP), and the etale and fppf covering-calculus statements in `spaces-topologies.tex` (`lemma-etale` and `lemma-fppf`). The item uses no SGA source.

Step 1 uses exactly the statements of def-trf-algebraic-space (surjective etale scheme atlases), lem-trf-space-fibre-products-etale-covers (fibre products remain algebraic spaces), lem-trf-space-representable-etale-scheme-tests (composition and arbitrary base change preserve representable surjective etale maps), and lem-sfb-space-local-properties-chart-test (the three chosen properties are equivalent to their scheme chart tests). I opened each cited node. The target chart is W to Z, and the source chart for X_W is the composite U to A to X_W. The latter is surjective etale because A to X_W is the base change of V to Y_W. These are precisely the chart-test hypotheses; no base-change theorem for P is silently assumed separately.

Step 2 uses exactly lem-trf-space-representable-etale-scheme-tests and lem-sfb-space-fppf-covering-calculus. Their actual statements give representability and surjective etaleness of the D_i to V_i projections and clauses (1), (3), (4) give an fppf covering of schemes after composition. The paired lift to A and the equality of V projections are written out as fibre-product identities; these are the elementary construction inside the step, not an uncited geometric theorem. In particular the map U to V itself is never assumed flat or of finite presentation. The hypothesis of local lifting is applied to a scheme V, an allowed test object in the fixed big site.

Step 3 uses the complete statement of the new 06NB scheme lemma and the existing chart-test node. Its inputs really are schemes U, V, W; P(U to W) was obtained in step 1; step 2 supplied a set-indexed fppf covering of V whose arrows factor through U over V. The conclusion of 06NB is P(V to W), exactly the premise of the chart test for Y to Z. No proof detail of a cited node is used as an extra conclusion. `citations.json` contains verbatim parts of all cited statements, with full statements for the two nodes supplying several clauses.

I checked delivery-errors B through E point by point. The one new node introduces all its own objects, explicitly defines its lifting hypothesis, cites the six definitions it uses, and contains no proof, proof dependencies or hidden sketch. Its source tag and label are correct. The three item steps have actual arguments, bool elementary flags and complete uses lists; all external mathematical inputs are cited by their statements and the two off-unit geometric tools are declared in split_report.tool_uses. No new node repeats an existing one; no proof is moved wholesale to a new node; the new lemma is the schemes-only input explicitly invoked by 06NR. There is no circular use of the item to establish that lemma. All step texts are below 2000 characters.

For small cases I checked identity u, split epimorphisms, empty X/Y/Z, disconnected etale charts, and an empty covering over an empty scheme. If X is empty, local surjectivity forces Y empty; a covering by empty members cannot cover a nonempty scheme. With empty Y or V the unique empty-family covering is permitted by the covering-calculus statement and 06NB still applies. None of the arguments requires a finite cover, quasi-compactness, a field base, separation or Noetherian hypotheses. Flatness uses the scheme lemma's independent flatness clause; the other two clauses do not add flatness of X to Z. The statement was retained unchanged after these tests.
