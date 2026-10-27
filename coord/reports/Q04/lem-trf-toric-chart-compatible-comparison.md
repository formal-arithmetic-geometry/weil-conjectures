# Q04 stage-1 delivery: lem-trf-toric-chart-compatible-comparison

## Files written

- dag/nodes/sec-trace-formula/lem-trf-toric-chart-compatible-comparison.json: item split into six steps, statement unchanged; no Mathlib match for the complete logarithmic assertion.
- citations.json: 18 step/node records, each with an exact excerpt of the cited statement.
- searches.jsonl: actual msearch.py searches for the full item, retained with their results; the script write_split.py is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0. Existing general lemmas suffice; the quotient relation calculation and two-projection calculation are elementary steps, not new nodes.

## Attachments

None. Searched lean/WeilConjectures for the item tag and LogStructure, LogScheme, toricChart and toric-chart language; no declaration states the item. Existing Sheaf declarations and Mathlib affine pullback results are not project attachments under this brief.

## WANTED

WANTED: Kazuya Kato, Logarithmic structures of Fontaine–Illusie (1988), section 1, for associated-log conventions used by this item. ILO VI 1.1 refers to it, but it is not an obtained document in literature/LIST.md. No download was attempted. The explicit construction in this split is agent-written, using the statements of the existing associated-log and monoid-sheafification nodes.

## Corrections and source comparison

No statement change, statement dispute, new hypothesis, or unit change. The item already assumes local Noetherianity of X; there is no need to prove it from g, nor to impose an isomorphism on group completions. The source field's VIII 3.3.8 and 3.3.11 concern log blowups; the more directly relevant chart-base-change discussion is VIII 3.3.3–3.3.6. Each new step names the actual place used. I read the current latest blueprint at main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345, especially sk-i-curve-zero/_section.md and lem-trf-local-term-locality.md/.proof.md. Their current route is contracting correspondences and they do not repeat this toric auxiliary statement. The item's historical ancestry is preserved and explicitly described in split_report.blueprint; nothing about the current chapter or unit route is changed.

The main citation hazard was using the universal property of associated log structures over the identity of a scheme to assert a map over f0:X→Y. That property alone does not assert this. The split instead forms the monoid sheaf H(U)=M(X×_Y U), verifies its sheaf condition from etale base-change continuity, and extends the explicit natural map from the quotient chart presheaf D to H by monoid sheafification. The relative-test definition then gives the required morphism. The comparison is identified using both projections, not by merely asserting it is canonical.

## Not duplicates

No new nodes, so there are no new/existing tag pairs. Whole-DAG title and statement searches and blueprint_refs searches for associated log, toric, chart, and isomorphisms are étale found existing tools rather than a second occurrence of the full item. In particular associated-log-universal-stalks is over one underlying scheme, prelog-pushout-hom-extension is a same-site extension into a log structure, and etale-log-presentation-comparison treats restriction/stalk comparison, not this tensor-product relative log morphism. They are not restatements of this item.

## Review by Q04

I read ILO VI 1.1 on printed p.69 (PDF p.75) for the etale-site log conventions and fs charts, and VIII 3.3.3–3.3.11 on printed pp.106–108 (in particular PDF pp.113–114) for toric chart realization and chart base changes. These conventions support the construction, but the full quotient and section-map argument here is written by Q04. I also read Stacks schemes.tex Tag 01I4, label lemma-fibre-product-affine-schemes, including its ring-map universal-property proof, and Tag 01JQ, label lemma-fibre-product-affines; morphisms.tex Tag 02GP, label lemma-open-immersion-etale; and verified the tag/label mapping in tags/tags. No SGA source is used. There are no new nodes needing further source reviews.

For step 1 I opened def-weil-pbc-module-tensor-product, def-weil-affine-spectrum, lem-weil-pbc-etale-base-change-finite-limits, lem-trf-associated-log-universal-stalks, and def-trf-fs-log-blowup. The tensor node supplies balancing and generation, and the multiplication is explicitly part of the item's own data. Spec contravariance supplies f0 and h; base-change-finite-limits supplies the actual etale test X_U. The associated-log stalk isomorphism is exactly the chart predicate in fs-log-blowup. Its hypotheses hold: beta is a monoid map by the displayed tensor multiplication and X is locally Noetherian by assumption. The fs conclusion uses that Q itself is fs, not any property of g's group completion.

For step 2 I opened lem-weil-pbc-etale-base-change-continuous, def-trf-fs-log-blowup and def-weil-size-convention. Continuity explicitly asserts that U↦F(X×_Y U) is a sheaf for any set sheaf F. The log node states precisely that M's underlying sets form a sheaf and restrictions preserve monoid operations; hence the set-sheaf assertion applies without needing a theorem about log direct images. Multiplication stays objectwise, so H is a monoid sheaf. The same assertion applies to the etale structure sheaf. The universe convention supplies a common larger universe and small skeleton, checking the small-site hypothesis of the sheafification theorem. The off-unit continuity and universe nodes are declared as generic tools in split_report.tool_uses; the other off-unit citations are Mathlib leaves.

For step 3 I reread the entire associated-log-universal-stalks statement, especially its quotient-presheaf sheafification and final chart clause, and the log axiom in fs-log-blowup. A global chart P→N identifies N with the stated sheafification. For e∈E_U its pulled-back structural value is a unit; the inverse units isomorphism therefore identifies the image of g(e) with that pulled-back unit. The formula sends both generating relation representatives to the same product, commutes with restrictions and preserves the monoid identity. This is a few-line computation from the cited statements, so it is marked elementary. It does not assume that every section of N(U) is globally a single pair.

For step 4 I opened lem-trf-commutative-monoid-sheafification, def-trf-fine-log-scheme-morphisms and def-pc-fibre-product. The first gives a bijection of monoid-sheaf maps with natural presheaf maps into every monoid sheaf, not merely a set sheaf. It supplies the extension and its uniqueness, including equality of the two structural maps into T by checking them on D. The definition of a fine log morphism explicitly gives the relative-test section-map formulation. For each V→U the fibre-product property supplies V→X_U, and equality of two such maps follows from their two projections; restrictions of the sheaf M then give the required naturality. fs implies fine, so this relative-test formulation applies to the fs structures here. This step states the full pair formula and checks the structural map and restriction equations; it does not rely on a hidden general associated-log functoriality lemma.

For step 5 I opened def-weil-affine-spectrum, def-pc-fibre-product and lem-weil-pbc-fibre-product-affine-spectra. The last explicitly includes the two projection ring maps, not just an abstract scheme isomorphism. Step 1 checks equality on each z^p; finite sums then check the base square. Both kappa and theta inverse compose to f0 and h, so fibre-product uniqueness gives their equality. This is the elementary uniqueness argument; theta kappa=id is deduced, not used to assume kappa is invertible.

For step 6 I opened def-weil-open-immersion and lem-weil-pbc-open-immersion-etale. An isomorphism has open image equal to its whole target and an invertible structure-sheaf map, so it meets the former definition, and the latter explicitly states the etale conclusion. This avoids quoting etaleness from its definition without establishing its hypotheses.

Small cases checked: P=Q=0 gives the identity chart comparison and the usual unit map; g=id gives the canonical identity base change; P=0, Q=N gives the affine-line toric base change; g:N→0 gives C=A/(alpha(1)−1) and the log-map relation remains valid (so injectivity of g is not needed). Taking alpha(1)=0 in that last case gives C=0 and the empty scheme. If alpha(p) is already a unit, its image under i is a unit and precisely the relation checked in step 3 is imposed. Torsion in a monoid's group completion was never excluded. None of these cases needs log regularity or a nonempty source.

I checked delivery-errors B through E point by point: no statement-only child carries proof text because no child is created; all notions remain covered by the unchanged statement dependencies and the proof's cited definitions; the source tags and labels were checked; every non-elementary fact is an existing node citation; every citation's statement was read and its used content copied verbatim into citations.json. No step relies on a cited node's proof. No new node restates a clause of the item. All proof steps are below 2000 characters (lengths 730, 569, 912, 1040, 687, 585), so there is no long step hiding a separate lemma. The only substantial assembly step is monoid sheafification into H, explicitly supplied by the cited Mathlib leaf. No unfinished mathematical argument remains.

## Validation

Server review_split and final deliver.py dry run are recorded by the delivery commands. Delivery is complete only when the final push prints DELIVERED.
