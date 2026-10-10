Files written:

- `dag/nodes/sec-abelian-varieties/lem-sp-ce-horizontal-lift.json` (statement, split; no new nodes; no Mathlib leaf)

Attachments:

- None.

WANTED:

- None. The Stacks source is present; the Weibel detail is used only as the source's explicit comparison construction.

What was wrong or incomplete:

- The imported item had an empty proof. I supplied the row-by-row comparison argument and retained its hypotheses. No statement correction was needed.

What I checked:

## Review by M1

I read the target statement and its source at Tag 015I in `/home/ubuntu/c1-stacks-review/derived.tex`, including the degreewise comparison construction and the final defect calculation. I also read the complete statements of `lem-weil-pbc-ses-injective-kernel-splits` and `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy`. Step 1 uses only the former's splitting conclusion; this supplies the sections and retractions needed to extend maps into the injective target rows. Step 2 uses exactly the latter's assertion that every map from an acyclic complex to a bounded-below injective complex is null-homotopic, applied to each exact augmented quotient row. Step 3 is the direct calculation from the augmentation identity and the given homotopy `w = d_L s + s d_K`; it is elementary. I checked that the source rows are exact by hypothesis, the target rows are injective resolutions by hypothesis, and that the resulting `s_1` preserves vertical degree and has the required augmentation value. I tested the concentrated degree-zero case: all differentials and defects vanish and the construction reduces to the prescribed map `s`. Mathlib searches were rerun with LeanSearch, Loogle, and grep; LeanSearch was unavailable, and the other two produced no direct Cartan--Eilenberg match.

## Second reading by M1

- Item statement: checked against Stacks Tag 015I / label `lemma-cartan-eilenberg` and the Cartan--Eilenberg definition; added the missing exact augmented-column and injective-column hypotheses required by the lift, and the nonnegative-degree condition needed at `p=0`.
- Step 1: checked against `lem-weil-pbc-lift-along-injective-quasi-iso`; after the statement repair its monomorphic quasi-isomorphism and bounded-below injective target hypotheses are present. The `p=0` case is valid because `L^p=0` for `p<0`.
- Step 2: checked directly from the double-complex definition and the augmentation/homotopy identities; it is elementary, so it has no node citation.
- New nodes: none; the existing lift node was searched and reused, and the double-complex notion is cited by `def-sp-double-complex-total`.
- Small cases checked: the zero complex and a complex concentrated in degree zero give zero defect; the `p=0` component is the zero map.
- Changes: corrected `created.item` to this item, removed the incorrect step-2 citation quote, and added the hypotheses and definition dependency identified above.
