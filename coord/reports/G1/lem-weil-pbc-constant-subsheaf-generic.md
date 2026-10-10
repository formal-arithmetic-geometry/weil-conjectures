# Stage 1 report: lem-weil-pbc-constant-subsheaf-generic

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-pbc-constant-subsheaf-generic.json`: statement node, split into two proof steps; Mathlib search found no match.
- `citations.json`: verbatim citations for the three existing dependency statements used by the two steps.

## Attachments

None.

## WANTED

None.

## Problems found

The imported item was unsplit and had no proof. The parent node's blueprint route is sound, but its first paragraph relies on the openness of images of etale morphisms; this is now explicitly cited through `lem-weil-pbc-flat-lfp-open`. No statement was changed.

## What could not be finished

Nothing. No new unsplit nodes were required.

## Review by G1

I read the item source in Stacks `etale-cohomology.tex`, Tags 03RZ (Lemma 59.71.6, the local constant-subsheaf argument) and 03RY (Proposition 59.74.1(3), generic constancy inside the constructible-sheaf proof), and the parent blueprint proof. I also searched the slopmaster2 source by the item id and by the constant-subsheaf terminology; there is no sorry-free declaration stating this item.

Step 1 defines the loci $W_m$ and proves they are open. The use of etale neighbourhoods and their covering behaviour is exactly the statement of `def-weil-pbc-etale-site`; the non-elementary geometric input is that flat locally finitely presented maps are open, exactly as stated by `lem-weil-pbc-flat-lfp-open`. Etaleness supplies flatness and local finite presentation by the site definition. The representative-section and refinement argument is the elementary stalk definition of a subsheaf of the constant sheaf.

Step 2 sets $M'=H_{\bar\eta}$ and uses irreducibility to observe that every nonempty open contains the generic point. Since $M$ is finite, the intersection over $M'$ is a nonempty open. The loci for elements outside $M'$ are empty, so every stalk on this open is exactly $M'$. The resulting map from the constant subsheaf is therefore an isomorphism on every geometric stalk; the cited node `lemma-weil-pbc-geometric-stalk-conservative` states precisely that such a map is an isomorphism. I checked each citation against its node file and recorded the exact quoted sentence in `citations.json`.

I tested the edge cases $H=0$ (all $W_m$ empty and $M'=0$), $H=\underline M$ (all $W_m=W$ and $M'=M$), and a proper constant submodule; the construction gives the expected $W^\circ$ and $M'$. The Mathlib searches were run twice with alternate phrasings through LeanFinder, Loogle, and source grep; LeanSearch was unavailable and recorded as such. No duplicate node or Lean attachment was found.
## Second reading by G1

- Item statement: checked against Stacks Tags 03RY (Proposition 59.74.1(3)) and 03RZ (Lemma 59.71.6), including irreducibility, nonempty open, finite commutative coefficient ring, and finite module hypotheses; verdict: agrees.
- Step 1: checked against the proof paragraphs of Tags 03RZ and 03RY and the statements of `def-weil-pbc-etale-site` and `lem-weil-pbc-flat-lfp-open`; verdict: the etale-neighbourhood, constant-section refinement, and open-image argument are cited and sufficient.
- Step 2: checked against Tag 03RY and `lemma-weil-pbc-geometric-stalk-conservative`; verdict: finite generic intersection and stalk identification are correct, and the subsheaf map is justified by the local sections represented in the definition of the loci.
- New node `lem-weil-pbc-constant-subsheaf-generic`: statement is self-contained, TeX-formatted, sourced by tags and label, and has no proof embedded in the statement; edge cases $H=0$, $H=\\underline M$, and a proper constant submodule behave correctly. Existing-node and Mathlib searches were checked in `searches.jsonl`; no duplicate or closed declaration was found.

Changes made: none; the worker's statement, proof steps, citations, and search records passed the second reading.
