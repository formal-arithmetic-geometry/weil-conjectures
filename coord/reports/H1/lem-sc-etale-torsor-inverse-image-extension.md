Files written:
- `dag/nodes/sec-curve-estimates/lem-sc-etale-torsor-inverse-image-extension.json`: statement split, no new nodes, Mathlib searches found no match.
- `citations.json`: verbatim citations for all proof-step uses.

Attachments:
- None.

WANTED: `literature/stacks-project/sites-cohomology.tex`, Lemma 03AJ (the repository does not contain the cited literature checkout), for `lem-sc-etale-torsor-inverse-image-extension`.

What was checked:
- The source Lean tree was searched for the item id, its torsor and inverse-image terminology, and the `(blueprint: lem-sc-etale-torsor-inverse-image-extension)` tag. No declaration states this item, so it is not an attachment.
- Existing DAG nodes were searched before editing. The item is consumed by `lem-sc-etale-torsor-h1-functoriality`; its only substantive prerequisites are the existing inverse-image definition and the existing torsor-to-extension construction in `lem-sc-torsor-h1`. No child node was created because a child for the inverse-image identification would merely restate the item clause.
- Step 1 uses the stated construction of `E_T` and the inverse-image functor: the construction is by a free abelian sheaf and quotient, and inverse image is sheafified presheaf inverse image and preserves the relevant colimits; exactness of inverse image gives the pulled-back short exact sequence.
- Step 2 uses the explicit relation `[g\\cdot t]=[t]+g` in `lem-sc-torsor-h1`; applying inverse image to generators and relations gives the canonical identification with `E_{u^{-1}T}` and identifies the constant quotient with `\\mathbf Z_Y`.
- Step 3 uses the stated fibre-over-1 description of `E_T`; the grading map transports under the Step 2 identification, so its fibre is exactly `u^{-1}T`. This is the only elementary step.
- The Mathlib searches were run with `msearch.py` for LeanFinder, Loogle, and source grep; all returned no torsor-extension result. The small cases `u=\\mathrm{id}` and the trivial torsor reduce to the identity extension, confirming the construction's direction and fibre claim.

## Review by H1

I read the item, the existing `def-weil-pbc-inverse-image` and `lem-sc-torsor-h1` statements, and the neighboring `lem-sc-etale-torsor-h1-functoriality` consumer. The hypotheses are sufficient: `u` is a scheme morphism, `G` is an abelian étale sheaf, and `T` is a `G`-torsor, exactly the data required by the two cited constructions. Step 1 cites the inverse-image definition for the functor and `lem-sc-torsor-h1` for the exact sequence; Step 2 cites those same statements for the free-abelian quotient and its relations; Step 3 cites the torsor node for the fibre over `1`. I checked every citation quote against the node text and recorded it in `citations.json`. I corrected the initially imported empty proof by spelling out the transport of generators, relations, grading, and fibre; no unrelated files were changed.

## Second reading by H1

- Item statement: checked against Stacks `sites-cohomology.tex`, Lemma 03AJ (`lemma-torsors-h1`), including the free-abelian quotient construction and boundary class; verdict: hypotheses and conclusion match.
- Step 1: checked the construction against Lemma 03AJ and exactness against existing `prop-weil-pbc-inverse-image-exact`; verdict: repaired the incorrect implication from left adjointness to finite-limit preservation and cited the exactness node.
- Step 2: checked constant-sheaf identification against existing `lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`, and generators/relations against Lemma 03AJ and the inverse-image definition; verdict: repaired citations and made generator transport explicit.
- Step 3: checked the fibre-over-1 description against the `E_T` construction in Lemma 03AJ and `lem-sc-torsor-h1`; verdict: elementary transport is correct.
- New nodes: none; the split has no child nodes, so B1-B7 do not apply beyond the item node. Existing-node search covered `lem-sc-torsor-h1`, inverse-image exactness, and constant-sheaf pullback; no duplicate or Mathlib leaf was created.
- Small cases: identity morphism gives the original extension; the trivial torsor gives the split extension; empty and one-point cases preserve the stated fibre and quotient descriptions.
- Changes: added the exactness and constant-sheaf dependencies, corrected Step 1's justification, and expanded Step 2's local generator argument so every non-elementary dependency is cited.
- Tool uses declared: `prop-weil-pbc-inverse-image-exact` supplies generic exactness, and `lem-weil-pbc-sets-etale-inverse-image-constant-sheaf` supplies constant-sheaf pullback; neither replaces a unit-specific argument.
