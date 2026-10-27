# Worker report: lem-sfb-fibre-product-algebra-etale

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fibre-product-algebra-etale.json`: item split into five proof steps; not a Mathlib leaf. Its statement and statement dependencies are retained.
- `citations.json`: thirteen verbatim statement quotations, one for each step/node citation.
- `searches.jsonl`: searches recorded by the required msearch command.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. Existing results supply every non-elementary input; a duplicate node for the flatness/finiteness patching or the fibre criterion would add no mathematics.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, fibre/fiber-product algebra, Milnor patching and etale patching found no declaration stating this item under its unrestricted hypotheses. Project declarations about affine tensor products and scheme fibre products do not state ring-pullback patching. No compiler was run.

## WANTED

None. The required Stacks sources are present locally.

## What was wrong and what changed

The item was statement-only. Its statement agrees with Stacks Tag 08KQ, `lemma-properties-algebras-over-fibre-product` (5), forward patching direction, in Situation 08KH. No statement correction or dispute is needed. In particular, adding a nilpotence condition would lose the stated generality. The source's final paragraph omits the fibre identifications; the delivered steps explicitly establish them and invoke the existing etale-fibre criterion rather than treating that inference as elementary.

Read the chapter and unit records and the current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`. This is a supporting commutative-algebra prerequisite in the inherited alteration/stable-curve/pushout chain, not the unit's key statement; no unit realization fields change. `blueprint_refs.py ancestor` reports a null ancestor, which the item already records. Its existing precise `from.place`, `via`, and `same_as: []` are preserved. Whole-blueprint searches for `fibre product`, `fibre product algebra`, `etale fibres` and `08KQ` found no matching blueprint statement. DAG searches found the already-created flat/finitely-presented patching and base-change recovery inputs and they are reused.

## Mathlib searches

The item's earlier search record is preserved. Six additional searches actually ran through msearch and are recorded from `searches.jsonl`: two patching phrasings through LeanFinder, `Algebra.Etale, RingHom.Etale` through Loogle, a fibre/pullback-and-etale grep, compatible-algebra gluing through LeanSearch, and a separate LeanFinder query for the flat/finitely-presented fibre criterion. All services returned results. Hits cover base change, composition, local standard presentations and the etale locus, not the item. I read the corresponding definitions and base-change declarations in `Mathlib/RingTheory/RingHom/Etale.lean` and `Mathlib/RingTheory/Etale/Basic.lean`. The existing DAG criterion makes a new fibre-criterion node unnecessary.

## Review by NE

I read `literature/stacks-project/more-algebra.tex`, Situation 08KH, Tag 07RU (`lemma-module-over-fibre-product`), Tag 01Z8 (`lemma-diagram-localize`), and the complete statement and proof of Tag 08KQ (`lemma-properties-algebras-over-fibre-product`). In particular, the proof's Ad (3) supplies flat finite presentation, Ad (4) splits field-valued fibres by the image of the kernel, and Ad (5) applies that calculation to etaleness. I also read Morphisms Tag 02GM (`lemma-etale-flat-etale-fibres`), Tag 02GJ (`lemma-etale-characterize`), and Algebra Tag 00U2 (`lemma-etale`), including flatness and base change. No SGA source is used. There are no new nodes whose sources need a separate review.

Step 1 uses `lem-weil-pbc-etale-algebra-flat` for flatness of the two component ring maps, and `def-weil-etale-morphism` plus `lem-weil-pbc-lfp-affine-opens-finite-presentation` for finite presentation on the whole affine charts. I opened their statements: the latter asserts finite presentation for every affine source/target pair, so its application is valid without quasi-compactness assumptions on other schemes. `lem-sfb-fibre-product-algebra-flat-presentation` has exactly the same arbitrary surjection and compatible algebras as the item, and its second equivalence supplies flatness and finite presentation of E over R. `lem-weil-pbc-flat-ring-map-iff-flat-affine` is the single-affine equivalence, not merely a definition or the only-if direction of an affine-chart criterion. `def-sbc-locally-finite-presentation` allows the whole source/target affine charts, immediately giving the remaining hypothesis for the final scheme criterion.

Step 2 uses the actual statement of `lem-sfb-patched-module-base-change`, whose two displayed canonical maps recover both component modules without flatness. With N=D and M'=C', the maps preserve products and units on pure tensors, so their bijectivity gives algebra isomorphisms. The step separately verifies surjectivity of R to B by lifting r(b) along q; hence its kernel J has R/J=B. No unrecorded algebra-patching equivalence is being extracted from the proof of the module node.

Step 3 uses `lem-weil-pbc-etale-ring-base-change`, whose statement is exactly etaleness of Spec(S tensor_R A) over Spec S. The map to the field factors through B because it kills J; this supplies the B-algebra structure on k needed by that lemma. I wrote the tensor reassociation map and inverse, with the induced map named bar u, to keep the base-ring map well-typed. The recovered algebra from step 2 is D, so the etale hypothesis is precisely B to D.

Step 4 uses the localization clause in the statement of `lem-sfb-ring-fibre-product-spectrum`, not just its topological pushout assertion. After swapping its factor ordering, its hypotheses hold because A' to A is onto. At h=(0,i), the B and A localizations invert zero, hence are zero; the resulting ring is A'_i. Since the image of h in the field is nonzero, the field map extends through that localization, giving an A'-algebra structure on k restricting to the original R-algebra structure. Tensor reassociation and the canonical recovery map of step 2 identify the fibre with C' tensor_{A'} k. The base-change lemma then applies to the given etale A' to C'. No assertion that R to A' is flat or surjective is made or needed.

Step 5 uses `lem-weil-pbc-fibre-product-affine-spectra` to identify the actual residue-field fibre, with its structural map, with the spectrum of E tensor_R kappa(y). For each y, the preceding two cases prove precisely the etaleness of this fibre. I opened `lem-sbc-flat-fibre-etale-neighbourhoods`: its statement assumes a flat locally finitely presented scheme morphism, allows empty fibres, and supplies an etale open neighbourhood of every x over y. Step 1 establishes those hypotheses. Finally `lem-weil-pbc-etale-local-on-source` says that etaleness on an open cover implies etaleness of f; the obtained opens cover by construction. The off-unit fibre criterion is declared in `split_report.tool_uses` as the generic scheme criterion; it does not replace the unit's alteration or six-functor route. Every other off-unit citation is a definition or Mathlib leaf.

I checked B--E of `coord/delivery-errors.md` against the saved node and open source statements. Every non-elementary input is an existing cited statement, and the thirteen quotations are copied verbatim from those statements. No new elementary, duplicate, self-repeating or statement-only node is introduced; consequently no new-node duplicate pairs require a `Not duplicates` section. The item keeps its hypotheses and meaning, and all TeX uses single backslashes after JSON decoding. All five steps are below 2000 characters. The tensor comparisons and localization-to-zero calculation are elementary arguments written out inside the steps; no hidden smoothness or dimension theorem is claimed.

Small cases checked: I=0 gives R=B and E=D. If B=A with identity map to A, R=A' and E=C'. If A=0, R=B times A' and the two field-map cases select the appropriate component. If C'=0 or D=0 the same recovery and fibre computations still apply and may give empty fibres; they do not assume either projection of E is injective. If R=0 there is no unital map from R to a field and the affine source is empty. An arbitrary nonnilpotent kernel, such as A'=k[t] to A=k, t mapping to zero, is handled by both cases: residue maps killing t factor through B, whereas maps with nonzero image of t extend through A'_t. None of the arguments needs Noetherianity, finite generation of I, a finite field extension, or a nonempty fibre. I also traversed dependencies of the recovered-module, localization and fibre-criterion inputs and found no path back to the item.

## Unfinished work

None in this stage-1 split. The cited existing unsplit inputs remain their own DAG work items. Server validation and direct delivery follow this report.
