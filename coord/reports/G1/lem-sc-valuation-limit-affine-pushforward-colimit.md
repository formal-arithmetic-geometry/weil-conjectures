Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-valuation-limit-affine-pushforward-colimit.json` (statement, split; no new nodes)
- `citations.json`

Attachments: none.

WANTED: none.

## Not duplicates

No new nodes were created, so no duplicate pairs apply. The existing affine limit, relative-spectrum, affine-section, quasi-coherent algebra colimit, and tensor-colimit nodes were searched and cited.

## Review by G1

I read the item source reference to Limits Lemma 01Z0 and the related 01YX/01YW construction, and compared the item hypotheses with the existing statements for affine limits and relative spectra. Step 1 uses the existing limit node for affine transition systems, the quasi-coherent algebra colimit node for the sheaf algebra and its affine sections, and the relative-spectrum node for the identification of the limit and its structure-sheaf pushforward; each cited statement explicitly supplies the relevant conclusion. Step 2 uses the relative-spectrum statement that inverse images of affine opens are affine and the affine-section pullback formula, whose statement gives the tensor isomorphism and naturality used for transition compatibility. Step 3 uses the algebra-colimit node's affine-section colimit and the tensor-colimit node's module colimit conclusion. Step 4 is only substitution of these identifications. I checked the fixed index tail remains directed and cofinal, and that all tensor products are over the section ring on an affine open. The small affine case reduces to the ring identity $(M\otimes_A B_i)$ and its directed colimit, so no additional hypothesis is introduced. Mathlib searches were run with LeanFinder, Loogle, LeanSearch, and grep in both requested phrasings; LeanSearch was unavailable and is recorded as such in the node's search list.

## Second reading by G1

- Item statement: checked against Limits 01Z0 (lemma-descend-section), including the directed tail, qcqs and affine-transition hypotheses, all three clauses, and the tensor products over $\mathcal O_{S_0}$; verdict: agrees.
- Step 1: checked against Limits 01YX/01YW and the statements of the affine-limit, relative-spectrum, quasi-coherent-algebra-colimit, and Spec-colimit-limit nodes; verdict: repaired to spell out the affine-open limit and local Spec identification.
- Step 2: checked against Limits 01Z0's affine projection formula and the full relative-spectrum anti-equivalence plus affine pullback-sections statement; verdict: repaired to cite the anti-equivalence actually used.
- Step 3: checked against Limits 01Z0 and Algebra 00DD, with the affine-section compatibility and directed tensor-colimit calculation; verdict: agrees.
- Step 4: checked as direct substitution of Steps 2 and 3; verdict: elementary.
- New nodes: none; all cited nodes were searched in `dag/nodes` and their statements were read, so B1-B7 are vacuous.
- Small cases: identity affine system gives the usual pushforward-tensor identity; $\mathcal F_0=0$ gives zero on every side; affine $S_0=\operatorname{Spec}A$ reduces to $M\otimes_A\varinjlim B_i\cong\varinjlim(M\otimes_A B_i)$.
- Changes: added `lem-weil-pbc-spec-colimit-limit` to the statement/proof dependencies and citations, expanded Step 1's local argument, and added the exact anti-equivalence citation used in Step 2.

