# Q159: lem-sfb-proper-generic-map-big-open

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-generic-map-big-open.json`: statement, split; seven proof steps; statement unchanged; no Mathlib match.
- `citations.json`: 33 entries, quoting the actual statement of every node used by every step.
- `searches.jsonl`: actual logged Mathlib searches for the item; the pre-existing search records in the repository item are retained.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. No Lean written or compiled; repository and launcher files were only read. The sandbox initially contained no item, report, or search log, only dispatcher markers, so there was no previous split to resume or dry-run first.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, codimension-one extension and fibrewise density found no declaration stating this item. Existing codimension-one etale-extension and divisor declarations concern other statements. The Mathlib spreading declarations supply only a local step, not an attachment of this project item.

## WANTED

WANTED: Bosch–Lutkebohmert–Raynaud, *Neron Models*, 1.2 Lemma 5 and Proposition 8, printed pp.14–15 (PDF pp.20–21), for lem-sfb-proper-generic-map-big-open. The repository has no copy of the PDF its inherited source names. I read the primary scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf (including the displayed page 21). No document was downloaded into the repository. The proof is marked agent-written and its operative references are the available Stacks sources, with BLR explaining the intended route.

## Findings and changes

The statement is correct; there is no STATEMENT-DISPUTED correction. The imported item had no proof. Its assertion for an arbitrary proper target follows from the argument before BLR invokes Weil extension; we never use that extension theorem for group schemes. Horizontal codimension-one points are already on the generic fibre. Only vertical codimension-one points require properness.

The generic fibre is not generally an open subset of the total space. Accordingly, the argument does not apply a rational-map lemma with that fibre as its supposed open domain. Instead it spreads morphisms from local spectra, compares them on each integral generic fibre using its fraction field, and proves overlap compatibility by relative separatedness and dense generic-fibre image. This also avoids the absolute separatedness hypothesis of Mathlib's canonical maximal partial-map representative.

The ambient chapter and unit were read, including the latest blueprint files under `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`. The unit's current text concerns six-functor stability; this auxiliary geometric argument changes no unit statement or route. The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor lem-sfb-proper-generic-map-big-open` returned `None`. I retained the complete existing provenance chain and its precise BLR place, and checked the whole blueprint with searches for rational map, codimension, Dedekind, spreading and normal morphism. No blueprint node duplicates this item. No unit realized fields are appropriate for this auxiliary node.

The Mathlib queries were run through msearch.py and their answers read. Two different semantic phrasings return RationalMap.ofFunctionField, PartialMap.fromFunctionField, rational-map representatives and the valuative specialization criterion. They do not give the big-open or fibrewise density assertion. The Loogle query returned zero results; the source grep returned zero results. I also read Mathlib/AlgebraicGeometry/SpreadingOut.lean:334–386 and 163–175: its local spreading result is already represented by lem-sfb-local-ring-map-spread. No leaf is invented from an incomplete match.

## Existing tools reused

The proof uses the existing local spreading and proper valuative criterion nodes, the existing normal-ascent and component-decomposition nodes, the existing separated-target equality and scheme-morphism gluing nodes, and existing local algebra for DVRs, fibre stalks, and principal ideal height. `split_report.tool_uses` declares generic tools from other units and explains why the six-functor unit supplies no substitute. No duplicate node is created; in particular neither the existing lem-per-local-ring-map-spread / lem-sfb-local-ring-map-spread pair nor the normal-modification nodes are replicated.

## Review by Q159

I checked delivery-errors B through E against the actual item, every cited statement, and the available source text. Since there are no new nodes, the statement-only, independent-hypothesis, duplicate-tag and new-leaf gates introduce no new obligations. The item retains its TeX statement and all inherited metadata. Its proof dependencies are exactly the union of step citations. I copied actual full cited statements into citations.json after reading them, rather than relying on the contents of their proofs.

For step 1, I read the localization-normal-domain statement (which explicitly includes arbitrary prime localization), smooth-normal-ascent (no connectedness hypothesis), smooth-flat (flat and locally finitely presented), locally-Noetherian ascent, the locally-Noetherian definition, normal topologically Noetherian component decomposition, flat-lfp openness, and scheme sobriety. These say precisely what the step uses. In particular the smooth-normal statement works over a Dedekind base and is not the misleadingly titled curve-only lem-sc-smooth-normal or lem-sc-smooth-regular. The affine smooth source is Noetherian and its normal components are clopen. Openness shows each nonempty component dominates the base and that its generic fibre meets every nonempty open. This establishes all density hypotheses used later. Stacks descent.tex Tag 034F, properties.tex Tag 0357, and morphisms.tex Tags 01T6 and 01UA were read at their labels.

For step 2, the canonical-local-spectrum statement gives its factorization through every neighbourhood and its fraction description; the integral-stalk statement explicitly identifies the fraction fields of all stalks with k(C). The base-change definition supplies the factorization over E. Thus both the component generic map and the maps at every point of the generic fibre come from the given f_E, not from an unrelated rational map. I checked that no finite-type or finite-presentation hypothesis on Spec E -> T is required.

For step 3, the normal dimension-one local-ring statement gives a DVR only after the step checks dimension is exactly one. A dimension-zero local domain is a field: its maximal prime must be zero, so every nonzero element is a unit. On an integral component such a point is its generic point and hence lies on the generic fibre. The DVR definition supplies the valuation-ring interpretation, and the proper valuative existence statement allows any valuation ring and relative proper target. The integral-stalk theorem gives the required same fraction field K, and the canonical local spectrum gives the map to T. I read algebra.tex Tag 00PD, including its valuation-ring and normal-local-dimension-one clauses, and morphisms.tex Tag 0BX7 for the intended valuative construction. No regularity, smoothness or group hypothesis on Y is smuggled in.

For step 4, the existing local-ring-map-spread statement was read in full: its source need only be locally Noetherian and target locally of finite type, and it preserves the entire given map from the local spectrum. Properness has both the separated and finite-type clauses in its cited definition. Stacks Tag 0BX6 case (2)(c) and Mathlib SpreadingOut.lean:374–386 provide exactly that relative morphism form. The integral-stalk and localization statements justify the fraction-field comparison on generic fibres. The relative-separated-dominant-ext statement permits an arbitrary dense-image scheme morphism into a reduced source; it is not restricted to an open immersion, which is essential for the generic-point test. This shows the spread map agrees with the whole restriction of f_E on its generic fibre.

For step 5, I rechecked that each overlap is an open of one normal integral component and is reduced; distinct components have empty intersection. Step 1 gives density of its generic fibre; step 4 gives equality after that dense-image morphism. The cited separated-target statement therefore applies with base T, and the gluing theorem states both existence and uniqueness of a morphism on an arbitrary open cover. Uniqueness also glues the equalities of structure maps, so the resulting morphism is over T. Every point of X_E had its own neighbourhood in step 4, which proves V_E=X_E as an open subscheme, not just density of the generic fibre. All local-dimension-at-most-one points are covered either by step 2 or step 3.

For step 6, the Dedekind-localization statement applies at the closed point's maximal ideal of D, including nonprincipal ideals of D. Only the stalk is required to have a uniformizer. The fibre-stalk-quotient statement identifies the actual local ring of the fibre with A / m_t A, hence with A/(pi). The canonical local-spectrum statement identifies its points with generalizations of the chosen fibre generic point, so that quotient has exactly one prime. Thus the maximal prime of A is minimal over (pi). The principal-ideal height-bound statement and localization dimension-chain statement then give dim A <= 1. I read algebra.tex Tag 00KV and the cited fibre quotient statement; this argument does not assume a global equation for the closed fibre, catenarity or a globally principal prime of D. The existing sobriety statement provides fibre component generic points.

For step 7, I verified that the closure of a subset containing each component generic point contains each component. The generic base fibre was already all of X_E. All nongeneric points of a one-dimensional domain are closed, so these cases exhaust T. This last step is elementary and has no external citation.

Small-case checks included X empty, empty closed fibres, disconnected smooth affine X, T containing only the generic point (a local base with the closed point removed), relative dimension zero, horizontal height-one points, and D a nonprincipal Dedekind domain. None forces a missing connectedness, nonemptiness of fibres, global uniformizer or smoothness of Y. P^1 over a DVR also checks why we do not claim extension across codimension two: a map like [x:pi] may be indeterminate at a codimension-two point, which V may omit. Every non-elementary step has length below 2000 characters and uses explicitly named existing nodes; no argument is hidden in a long step or shifted into a new node restating the item.

## Unfinished work

None in the one-level split. Existing unsplit dependencies retain their own independent work; they are not proved here. Delivery validation is run with the mandated server dry run before pushing.
