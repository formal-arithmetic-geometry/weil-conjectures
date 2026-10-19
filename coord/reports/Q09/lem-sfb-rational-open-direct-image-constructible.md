## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-open-direct-image-constructible.json`: repaired existing item; no new nodes.
- `citations.json`: verbatim statement citations for every proof use.

## Attachments

None. I searched the project declarations under `WeilConjectures/`; no sorry-free declaration states this item exactly.

## WANTED

None.

## What was wrong and what was corrected

The returned split used the `sk-prop-open-coefficients` proof text while its authoritative unit and blueprint ancestry still pointed to `sk-thm-restriction`/`det-thm-restriction-local`. The item now records the open-coefficients unit route and its blueprint paragraph. The maintainer-owned authoritative unit field on the shared base must be refreshed to this same binding when the delivery is merged; the delivery itself leaves that field to the maintainer contract.

The earlier Step 2 wording did not explicitly state the direction needed for the input: the given `K` is already in the finite-constant-model `Dbc` of `sk-def-sfb-constructible`. I now say this and apply clause (4) of `sk-lem-integral-models` directly to `K`, while retaining the integral generator conclusions. The proof then follows the source's integral and rational paragraphs: integral open direct image, localization telescope, finite-subextension continuity, finite scalar matrices, and triangulated closure. The forbidden SGA 4/4½ route is absent. The Mathlib searches are recorded in `searches.jsonl` and the item JSON; they found no matching theorem.

## Review by Q09

I read the current item statement, the `sk-prop-open-coefficients` unit record and its `_section.md` and `.proof.md`, and every cited node statement. Step 1 checks the standing separated finite-type setting, Noetherian schemes, qcqs schemes, and qcqs of the open immersion. Step 2 now checks both sides of the input use: `K` is assumed in the finite-constant-model category, and clause (4) of `sk-lem-integral-models` produces the finite integral-lattice cone/shift construction for exactly that category; the integral open-image theorem applies to each lattice generator. Steps 3–4 use the stated localization, colimit, continuity, scalar-change, and finite-matrix assertions to identify and preserve finite constant local models. Steps 5–6 read the finite-free coefficient basis and filtered finite-subextension colimit statements and check compatibility with the derived direct image. Step 7 verifies flat extension to the algebraic closure preserves the same bounded finite models, and Step 8 uses the stated triangulated closure and derived-functor shift/triangle compatibility for the finite construction of `K`.

I checked the hypotheses at each use (finite coefficient field, fixed algebraic closure, Noetherian qcqs schemes, quasi-compact open immersion, and the two coefficient choices), copied every citation quote verbatim into `citations.json`, and tested the empty open, identity open, zero complex, and both coefficient cases. The route and blueprint binding were corrected after the return; no new node or duplicate was introduced.
