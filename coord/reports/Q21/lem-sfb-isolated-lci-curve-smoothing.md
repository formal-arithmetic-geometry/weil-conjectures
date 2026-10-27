# Worker report: lem-sfb-isolated-lci-curve-smoothing

## Files written

All node files are in `dag/nodes/sec-six-functors-basics/` in the Q21 sandbox.

- `lem-sfb-isolated-lci-curve-smoothing.json`: item; eight proof steps, status split. The statement is unchanged. Added the dimension and power-series notions to statement dependencies.
- `lem-sfb-lci-cohen-macaulay-stalks.json`: statement, unsplit; no Mathlib match. Depth equals dimension at every stalk, not just at a closed point.
- `lem-sfb-lci-local-fitting-smoothing.json`: statement, unsplit; no Mathlib match. Local deformation with an explicit parameter-power Fitting bound.
- `lem-sfb-isolated-curve-formal-lifting.json`: statement, unsplit; no Mathlib match. Compatible local deformations lift to a compatible global system.
- `lem-sfb-proper-formal-curve-algebraization.json`: statement, unsplit; no Mathlib match. A proper flat formal curve system algebraizes, with its reduction identifications.
- `lem-sfb-finite-jet-smooth-generic-fibre.json`: statement, unsplit; no Mathlib match. A finite-jet Fitting bound detects smoothness on the generic fibre of an existing proper flat family.
- `citations.json`: one verbatim quotation for each of the 26 step/node citations.
- `report.md`: this report and the author's review below. Search results, the original tool log `searches.jsonl`, and sandbox scripts are retained locally for reproducibility.

## Attachments

None. I searched `lean/WeilConjectures/` both for the item id/docstring tag and for smoothing, isolated singularities, local complete intersections, formal curves and curve deformations. The smoothing hits concern Popescu ring smoothing and the radicial generic-fibre construction. They do not state the projective smoothing theorem here. A declaration in `Sheaf/` or a sorried declaration would not qualify as an attachment under this brief; no attachment is claimed.

## WANTED

None. All sources used are present under `literature/stacks-project/`.

## Findings and route

The item accurately states the conclusion of Tag 0E7Y, `lemma-smoothing-proper-curve-isolated-lci`. Its finite-presentation conclusion follows over the Noetherian power-series base. No hypothesis or conclusion of the item was changed. There was no earlier sandbox split or report to preserve.

I read the complete proof of 0E7Y, including its warning that the algebraized local ring need not be the chosen deformation ring. The split retains that warning: only the reductions modulo powers of t are identified. The local-to-global and Fitting arguments are written out rather than replaced by a smoothing-existence black box.

The source handles the zero-dimensional part through the separate Artinian smoothing lemma 0E7W. Here the same local/formal construction used in the second paragraph of 0E7Y is applied to both pure-dimensional pieces. Its actual inputs 0DZP, 0E7X, 0E7R and 0E7T allow dimension zero. This is below the unit route and changes no unit step. The proof is consequently marked agent-written, following 0E7Y, rather than claiming verbatim transcription. This avoids introducing a second smoothing theorem solely for the zero-dimensional clause. The projectivity of the final two-piece union is proved by complementary coordinate subspaces, not left as an uncited permanence assertion.

The item's inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor lem-sfb-isolated-lci-curve-smoothing` prints None. I preserved its detailed existing place and via chain; the new nodes use that ancestor, the item prepended to via, and an explicit supporting-input place. Whole-blueprint searches for smoothing, deformation, algebraization, Fitting, Cohen-Macaulay, proper curve, complete intersection and dimension at a closed point found no blueprint node stating a new input. The dimension and differential calculus used here already exist elsewhere in the DAG. Generic off-unit statements are declared in `split_report.tool_uses`; no maintainer `tool_uses` field was written. This item is not the key statement of its unit, so no unit realization file was edited.

## Source error

The displayed statement of Tag 0E7R, `lemma-formal-algebraic-space-proper-reldim-1` in `spaces-more-morphisms.tex`, omits properness of the formal schemes/spaces. Its proof immediately calls the special fibre proper and then chooses an ample invertible sheaf on that proper curve. Read literally without that hypothesis, the statement is false: take the compatible constant systems of affine lines over k[[t]]/(t^n). A projective algebraization would have projective special fibre, whereas the affine line is not proper over k. The new algebraization node explicitly assumes every X_n proper, as supplied in the application. This repairs the source display for the supporting statement and does not change the smoothing item. I also read 0D4G: it gives flatness at points of the special fibre; the remaining points lie over the field k((t)) and are flat automatically. Thus I did not silently read 0D4G as a global-flatness theorem over an arbitrary base.

## Searches and duplicate checks

For the item and each of the five proposed supporting nodes I ran two distinct plain-language LeanFinder searches, a Loogle query, the required source grep through msearch.py, and LeanSearch. Every command and query is preserved verbatim in the node's `mathlib_searches` and in `searches.jsonl`; all these services answered. I read the returned names and signatures. The closest hits describe standard smooth algebras, the smooth locus, formal lifting for algebra homomorphisms, Krull dimension of localizations, or properness of Proj. None constructs local deformations, glues curve deformations, algebraizes a formal scheme, proves the lci depth equality, or detects smooth generic fibres from a Fitting jet. The broad algebraization grep returned the `algebraize` tactic; a second grep restricted to AlgebraicGeometry returned no formal-scheme/algebraization hits. No Mathlib leaf is asserted.

Before creating the nodes I searched the entire DAG by their concepts and exact tags 00SB, 0E7X, 0DZP, 06HN, 0E7R, 0D4G and 0E7T, and read the matching statements. This yielded existing nodes for the Cohen-Macaulay dimension partition, closed-point dimensions, lci local-ring criterion, differentials, Fitting base change, flat base change, properness and Noetherianity, all reused. The new nodes have statements only, empty proofs and proof-dependency lists, and explicit definition dependencies. None is one clause of the target renamed: the local lemma is about a local algebra and a singular ideal, the lifting lemma has prescribed arbitrary compatible local data, algebraization has no smoothness conclusion, and the jet criterion assumes an already existing proper flat family.

## Not duplicates

lem-sfb-isolated-curve-formal-lifting vs lem-sfb-isolated-lci-curve-smoothing: formal lifting assumes arbitrary prescribed compatible local deformations and produces compatible global infinitesimal schemes, without an lci hypothesis, algebraization, projectivity or generic smoothness. The item instead constructs an actual projective smoothing from an lci hypothesis and has no prescribed local data. The shared mention of 0E7Y records where 0DZP and 06HN are applied, not equality of their statements.

lem-sfb-lci-cohen-macaulay-stalks vs lem-trf-lci-pointwise-criterion: the existing node characterizes lci using local presentations, but does not conclude any depth equality; the new statement is precisely that Cohen-Macaulay conclusion.

lem-sfb-lci-cohen-macaulay-stalks vs lem-trf-completion-local-complete-intersection: the existing node compares completions at maximal ideals and gives depth equality there; the new statement gives equality at every scheme point, including nonclosed points, with no choice of completion or coefficient field.

lem-sfb-lci-cohen-macaulay-stalks vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: the existing node proves regularity of the defining sequence in an ambient polynomial local ring; it does not state that the quotient stalk has depth equal to dimension.

lem-sfb-lci-cohen-macaulay-stalks vs lem-weil-pbc-relative-global-complete-intersection-partial-local-flat: the existing node concerns flatness over a base of partial quotients; flatness over a field does not state the Cohen-Macaulay conclusion.

lem-sfb-lci-cohen-macaulay-stalks vs lem-weil-pbc-lci-conormal-free-rank-codimension: the existing conclusion is freeness and rank of a conormal module, not depth of the quotient local ring.

lem-sfb-lci-cohen-macaulay-stalks vs lem-weil-pbc-polynomial-ring-field-regular-ring: the existing node treats polynomial rings themselves, not general complete-intersection quotients and their stalks.

## Review by Q21

I reread the item against all four hypotheses of 0E7Y: the field is arbitrary, properness includes finite type and separatedness, the lci condition is the affine-cover condition, and the nonsmooth locus is a finite set of closed points. No algebraic closedness, perfectness, reducedness, connectedness or pure-dimension-one assumption was introduced.

For the new stalk theorem I read Algebra 00SB (`lemma-lci-CM`) and its proof, and checked that the term Cohen-Macaulay ring supplies every prime localization, as required by the existing fibre-piece node. For the local smoothing theorem I read 0E7X (`lemma-smoothing-at-lci-point`) including its final localization B=Q_q; that justifies saying B is local, not merely B/tB local. Its dimension is dim A plus residue transcendence degree, retained in the node. For formal lifting I read 0DZP (`lemma-curve-isolated`) and 06HN (`lemma-smooth-morphism-essentially-surjective` in formal-defos.tex), including the inductive construction of compatible formal objects. This is why the node supplies compatible local isomorphisms, not unrelated deformations at each order. Properness of the deformations follows from properness of their nilpotent special-fibre thickenings; no new nonsingular generic fibre is claimed in this node. For algebraization I read 0E7R and 0D4G and corrected the properness omission described above; projectivity and all reduction identifications are explicitly included. For the jet criterion I read 0E7T (`lemma-criterion-smoothing`): its essential hypotheses are properness, flatness and a Cohen-Macaulay equidimensional special fibre, and the required element is t^(n-1), not t^n modulo t^n.

Step 1 uses the new all-stalk depth equality, `lem-pc-flat-field`, and the Noetherian finite-type/finite-presentation lemma to meet exactly the flat/l.f.p./depth hypotheses of `lem-sbc-cohen-macaulay-equidimensional-fibre-pieces`. I opened that node: it supplies disjoint open pieces with component dimension d. There can only be pieces 0 and 1; their complements show they are closed. `lem-weil-pbc-closed-immersion-proper` explicitly includes properness of a closed subscheme of a proper scheme. The lci pointwise criterion shows that passing to an open keeps the same lci local rings. The empty scheme is handled before making a choice of d.

Step 2 uses that same pointwise lci criterion, the equidimensional-open local-dimension node and the closed-point dimension node: none is being substituted for another. They supply exactly dim A_i=d. On an affine neighbourhood the residue field is a field quotient of a finite type algebra; the opened Zariski-lemma node gives its finite degree, hence transcendence degree zero. These are the two terms in the dimension parameter required by the local smoothing node. This is where closedness of each p_i matters.

Step 3 uses the actual base-change theorem for flat modules, not merely the definition of flatness. Reduction is tensor product; finite type presentations localize and reduce; a nilpotent thickening of a local ring is local. The formal-lifting statement really supplies both the global compatible schemes and the local compatible algebra identifications used later. Its hypotheses separatedness, finite type, dimension at most one and smoothness off the finite list are all available from the proper piece. An empty list is allowed.

Step 4 uses algebraization only after properness and flatness of every formal stage have been supplied. The special fibre has dimension at most one. `lem-kun-projective-implies-proper` states properness for the same finite-projective-space convention used by the item. No step equates the untruncated local rings with B_i.

Step 5 uses the opened localization and base-change statements for Kähler differentials, and clause (2) of `lem-trf-fitting-ideal-independence-base-change`. They give precisely the reduced differential module and its Fitting ideal. Multiplication by t^(n-1-e_i) is the elementary part. The choice of n includes 0 so it is defined when the singular list is empty.

Step 6 applies `sbc-lem-smooth-criterion` to the open of the flat deformation lying over the smooth open of Z. Its base has one point and residue field k, so every fibre is the one smooth fibre required by that criterion. The dimension node computes its fibre dimension d; the opened differential theorem then gives free rank d stalks. The unit Fitting ideal follows from the identity presentation in the existing minors statement. This also works when d=0.

Step 7 first uses `lem-weil-pbc-finite-type-over-noetherian` to justify Noetherianity of Z_n; R_n is finite-dimensional over k. The Fitting-sheaf definition identifies the stalk ideals already checked. The cyclic image of the section in the coherent quotient has closed support, so membership at all closed points implies global membership. The criterion is then applied to the existing Y_d with the same d and the same t^(n-1). Its Cohen-Macaulay and pure-dimension hypotheses came from step 1, not from an assumption that the generic fibre was already smooth.

Step 8 is elementary assembly: the two families are embedded in disjoint complementary coordinate subspaces. This proves the finite-projective-space conclusion even with two different component dimensions. Flatness, finite presentation and smoothness on the generic fibre are local on this finite disjoint open cover. I checked that no non-elementary step exceeds 2000 characters.

For small cases I checked the empty scheme, an already smooth proper curve (empty singular list and n=1), a finite inseparable field viewed as a zero-dimensional lci k-scheme, the nonreduced local complete intersection k[x]/(x^2), and a disjoint union of a one-dimensional smooth component and a zero-dimensional component. The local smoothing and formal-lifting statements do not require perfect k. The finite-jet condition has the correct exponent in each case. The completion comparison node's extra hypotheses were not borrowed to justify the all-stalk theorem. No new statement presupposes the smoothing conclusion of the item.

I corrected a nonexistent definition-id spelling while checking statement dependencies, added explicit properness inheritance and flat base change citations, and added Noetherianity for the closed-support argument. All quotations in citations.json were regenerated from the actual cited statements after these corrections. The new nodes contain no proofs or proof sketches. The sandbox contains no Lean edits and no compiler or Lake invocation was run. The only automatic checks requested were on the server via the authorized tools.

## Unfinished work

No part of the requested one-level split remains unfinished. The five new inputs intentionally remain statement-only unsplit nodes for later work. Independent mathematical review belongs to the maintainer.
