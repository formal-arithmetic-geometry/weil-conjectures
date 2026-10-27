# Stage-1 report: lem-per-prelog-stalk-chart-spreading

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-prelog-stalk-chart-spreading.json`: statement retained verbatim; six proof steps; status split; generic off-unit tools declared in `split_report.tool_uses`. Added the geometric-stalk definition to statement dependencies.
- `citations.json`: one verbatim statement quotation for each of the thirteen step/node citations.
- No new nodes; no Mathlib leaves. The new searches and the inherited searches both have no match for the item. Search results are recorded in the item and `searches.jsonl`.

## Attachments

None. Searches for the exact blueprint tag and for `prelog`, `LogStructure`, `log_structure`, fine/fs log structures in `lean/WeilConjectures/` found no declaration stating the item. The broader chart/stalk search returned polynomial and manifold charts, which are different notions. The existing finite-presentation lemma is reused through its DAG node; it is not an attachment for this item.

## Wanted literature

WANTED: K. Kato, *Logarithmic structures of Fontaine--Illusie* (1988), sections 1--2, associated-log universal property and stalk chart criterion, for lem-per-prelog-stalk-chart-spreading. It is not in the obtained literature. No download was attempted. The proof delivered here is explicitly agent-written from the statements of the existing DAG nodes, not attributed to an unread Kato proof.

## Findings and corrections

The imported statement is correct; no STATEMENT-DISPUTED correction is needed. Its cited ILO passages give the chart conventions and use chart extension, but ILO VI 1.1 explicitly imposes local Noetherianity by default. Thus these passages alone do not establish the item's arbitrary-scheme claim. The new `proof_origin` states this limitation and records the argument as agent-written.

I read the current `literature/blueprint/latest/` unit and the ancestor `lem-per-artin-gabber-affine-curve` proof, not an older snapshot. The inherited ancestry points through the regular-pair/Kummer branch assigned to the ancestor's Step 3. The current blueprint Step 3 is a duality argument and has no explicit logarithmic chart lemma. The split supplies the already requested local input; it changes neither the chapter nor the unit route. Whole-blueprint searches for `monoid`, `stalk chart`, and `log structure` found no imported blueprint theorem stating this arbitrary-scheme input.

The key algebraic input already exists: `lem-trf-fg-commutative-monoid-finite-presentation` gives finite relations and their universal property for any commutative monoid, including nonintegral ones. The required arbitrary-scheme associated-log construction, stalk formula, restriction comparison and mapping universal property already exist in `lem-per-integral-chart-logification-thickening`. There is no need to create a node repeating either clause of this item.

## Not duplicates

No new nodes were created. For comparison, `lem-trf-finite-monoid-stalk-data-spreading` assumes that X is locally Noetherian, and `lem-trf-fine-log-stalk-chart-spreading` makes that same assumption. `lem-trf-charted-log-map-local-right-inverse` also assumes local Noetherianity. None can be cited for the arbitrary-scheme assertion. Their proof route motivated the finite inverse-map argument, but the delivered proof invokes only the generic statements that actually apply. The general commutative-monoid finite-presentation node is cited rather than duplicated.

## Review by N7

I checked B--E of `coord/delivery-errors.md` against the six steps and the actual statements of every cited node. There are no new nodes to audit for self-contained statements, presentation-only status, or missing monoid definitions. I preserved the imported fields and statement, filled the split record, and recorded the real Mathlib query strings and returned signatures. The search results about submonoid presheaves, etale rings and manifold charts do not prove this theorem; the second LeanFinder query finds filtered-colimit element constructors, not the logarithmic assertion or finite monoid presentation.

For the item I read ILO VI 1.1 (printed p.69; PDF page 75), VI 3.7(a) (printed p.75; PDF page 81), and VIII Remark 3.3.4 (printed p.107; PDF page 113). The first passage defines fine/fs structures via charts and explicitly states its default Noetherian convention. The final sentence of VI 3.7(a) uses spreading of a stalk splitting to a chart without explaining the finite-data argument. VIII 3.3.4 gives etale-local fine charts. The proof here supplies the missing argument under the arbitrary-scheme conventions of our existing nodes. There are no new-node sources to read.

Step 1 uses the actual colimit definition in `def-weil-pbc-geometric-stalks`, cofilteredness in `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`, and all three elementwise clauses in `lem-weil-pbc-filtered-colimit-sets-elementwise`. I read Stacks `etale-cohomology.tex`, Tag 03PQ (`lemma-cofinal-etale`), `definition-stalk` and its following paragraph, and `categories.tex`, Tag 04AX (`section-directed-colimits`), especially the explicit eventual-equality relation. The size convention supplies a small representative site, and the lifts of the fixed point to each representative form a set, so the small filtered index hypothesis really holds. For restriction and rebasing I read `lem-weil-pbc-sets-etale-inverse-image-restriction` and `lem-weil-pbc-sets-etale-inverse-image-stalk-germ`; these are statements about sheaves of sets, so they apply to the underlying sets of any monoid sheaf. Their germ identifications preserve products because products are formed on representative sections. This avoids citing the abelian-only restriction lemma for monoids.

Step 2 uses precisely the finite-relations and extension-if-relations-hold clauses in `lem-trf-fg-commutative-monoid-finite-presentation`, whose full statement and existing proof I read. Its finite generating tuple may be empty and it assumes no cancellation or saturation. Step 1 first provides the generator representatives, then makes the finite relation equations true. Thus a genuine homomorphism is produced, rather than a tuple falsely asserted to be one. The calculation works for arbitrary monoid sheaves, a scope explicitly stated in Step 1. It is therefore available for the auxiliary associated-log sheaf N later in the proof, without invoking the item circularly.

Step 3 is only finite iteration of the already established representatives/equalities, and equality of homomorphisms on a generating tuple. It is marked elementary for this reason. For simultaneous requests, old relations remain true on restriction. No new lemma or general colimit theorem is concealed here.

Step 4 uses `lem-per-integral-chart-logification-thickening` exactly for its first three paragraphs: N exists on any scheme for a finitely generated integral B, its stalk is the displayed pushout, its universal property supplies f, and restriction keeps that presentation. The hypothesis on B is now in force, although it was not needed earlier. The given pushout isomorphism is exactly f on the marked stalk. The fs definition and chart meaning in `lem-per-associated-log-arbitrary-scheme` supply a chart covering with a finitely generated integral Q. `lem-weil-pbc-etale-cover-geometric-point-lift` supplies a pointed member, retaining the same geometric field; I read its statement and Stacks Tag 03PR (`lemma-geometric-lift-to-cover`). This is a covering argument, not an unjustified choice of a chart containing the point.

Step 5 reuses the already proved finite monoid spreading argument for Q into N. It first imposes fk=q as an equality of homomorphisms; only then does compatibility with structural maps follow from f being a log homomorphism. The associated-log universal property for the Q-presentation of M gives g and shows fg=id because both maps agree on Q. Its stalk is f inverse, by this equality and the already assumed invertibility of f on the marked stalk. No finite generation of a group of units is required.

Step 6 applies the already proved equality-on-generators argument to B into N, imposing gf on its B-generators equal to the identity. The same associated-log universal property now for the B-presentation of N gives gf=id. Both composites have actually been checked; an isomorphism at one stalk was not simply asserted to hold on a neighbourhood. The map on B is the original lifted map restricted throughout, so the specified germ is retained. If B is fs, the resulting chart is an fs chart by definition. All the geometric tools and the logification statement were verified to have no local Noetherian hypotheses.

Small cases checked: the trivial monoid and an empty finite list; a noncancellative idempotent monoid (its relation must be imposed, not ignored); a finitely generated group monoid (inverse relations are among the finite relations); a trivial log structure (arbitrary unit groups need not be finitely generated); and a non-Noetherian affine scheme, where the proof only manipulates finitely many section equalities and uses no coherence assertion. A nontrivial idempotent monoid mapping to an integral log stalk is forced to send its idempotent to the identity, which the relation step still handles correctly. The integral hypothesis is used only when forming N, not in the spreading clause.

Every cited node's statement was opened and compared with its use, and every quote in `citations.json` was checked as a literal substring of that statement. A read-only dependency traversal found no path from any of the cited inputs back to this item. Off-unit inputs are declared only as generic algebra, stalk and chart-cover tools; they do not replace a step of the perverse unit. All six steps are shorter than 2000 characters, and each is an explicit finite-data construction or an application of a stated universal property. No new node merely renames a clause of the item. No Lean was written or compiled, and all writes were confined to this item's sandbox.

## Unfinished work

None in this one-level split. The cited existing unsplit nodes remain their own items. Required server dry run and push are performed after writing this report.

The first dry run required longer quotations for the stalk definition and the inverse-image germ comparison. I expanded these to include the defining formula with its context, also including all used clauses of the elementwise and logification statements. The split itself was unchanged.
