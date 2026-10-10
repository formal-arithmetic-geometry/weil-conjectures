# Stage-1 delivery: lem-weil-pbc-affine-etale-site-base-change

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-etale-site-base-change.json`: split the item in four steps; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sets-etale-inverse-image-exact.json`: one new, unsplit statement; no Mathlib match. It records the exactness assertion for sheaves of sets on the full small etale sites from Stacks 03Q1(2).
- `citations.json`: one verbatim statement excerpt for each node cited by each step.

## Attachments

None. Searching the source checkout by the item id and by affine-etale site/base-change phrases found no declaration stating this item. The source declaration `AlgebraicGeometry.Etale.preservesFiniteLimits_upperStar` is conditional on preservation of finite limits by a Kan extension and does not state the new node unconditionally; its docstring also reports a sorried sheafification dependency.

## WANTED

- `literature/stacks-project/etale-cohomology.tex`, Tags 0EYL and 03Q1, for the item and `lem-weil-pbc-sets-etale-inverse-image-exact`. The literature tree in this clone contains only the lists and import tools. I read the Stacks text through the official tag pages and the available read-only TeX copy at `/home/ubuntu/c1-stacks-review/etale-cohomology.tex`.
- `literature/stacks-project/topologies.tex`, Tag 04HR and definitions 0219/021B, for the affine site. I read the official tag page and `/home/ubuntu/c1-stacks-review/topologies.tex`.
- `literature/stacks-project/sites.tex`, Tags 00WV, 00WW, 00WX and 00X1, for continuity, adjunction and the morphism-of-sites condition. I checked the official pages and the read-only TeX copy at `/home/ubuntu/c1-stacks-review/sites.tex`.

## Imported material corrected

The imported item had no proof and listed permanence and continuity lemmas as statement dependencies even though its sentence names neither. The new proof cites these as proof dependencies. The main missing inference was exactness: Stacks 00X1 requires an exact inverse image as well as a continuous functor. I added the 03Q1 statement-only node and transported its conclusion through the affine-site equivalences of 04HR. The proof origin is marked `agent`, because this transport argument is written here and is not the proof of 0EYL itself.

## Review by F1

I read Stacks 0EYL (colimit of affine etale sites with affine transitions), 04HR (the affine subsite gives an equivalent topos), 03Q1(2) (set-valued inverse image on full small etale sites is exact), and Sites 00WV/00WX/00X1. The item's hypotheses match them: the only extra assumption for preserving affine objects is that $h$ is affine. The new 03Q1 node states its source with the same arbitrary-scheme-morphism hypothesis, and no proof sketch is hidden in its statement. I checked its tags against the TeX labels: 03Q1 is `lemma-stalk-pullback`, 03PZ is `section-inverse-image`.

Step 1 cites the finite-limits node for etaleness and the affine-morphism-permanence node for the two needed implications, base change of an affine map is affine and an affine map with affine target has affine source. The affine-site-topos statement identifies the affine objects as a full subcategory; no property of its proof is used. Step 2 cites that same statement for *finite standard coverings*, the etale-covering-base-change statement for etaleness and joint surjectivity, the definition of affine morphism for maps between affine schemes, permanence for affine fibre products, and the finite-limits statement for the comparison isomorphism. I checked that all fibre products mentioned there have affine targets at the point permanence is applied.

Step 3 applies the continuity conditions as they are written in `def-weil-pbc-sites-and-cohomology` to Step 2. Its cited continuous-functor adjunction statement supplies the left adjoint; the definition alone would not. Step 4 uses the *sheaves of sets* equivalence expressly stated by the affine-site-topos node, the full-site direct-image formula expressly stated by the etale-base-change-continuous node, and the finite-limit/colimit exactness expressly stated by the new 03Q1 node. The equality of the two right adjoints is checked objectwise on affine $V$, including the arrows. Taking left adjoints and transporting universal properties through equivalences then gives exactness, which is the further condition in the cited morphism-of-sites definition. I did not infer this from continuity alone.

For B1-B9 I checked that the sole new node is a self-contained statement with its own $h,T,T'$, source tag and label, definition dependencies, empty proof, Mathlib searches, and a precise blueprint ancestor and place. Its three kinds of Mathlib search found only a generic conditional sheaf-pullback theorem; LeanSearch returned HTTP 500 twice, which is recorded rather than turned into a claim of absence. The DAG and blueprint searches by 03Q1 and exact set-valued pullback found no exact existing node. For C1-C8 I opened each cited statement, prepared `citations.json` from its actual wording, checked no step uses a cited proof, and checked that the new dependency does not point back to this item. Off-unit generic tools are declared in `split_report.tool_uses`.

For D1-D5 the new node is strictly smaller than the item: it says only the already-known exactness of pullback on full small etale sites; Steps 1-4 still construct and verify the restricted functor and the transfer argument. For E1-E6 I tested the statements against $h=\mathrm{id}_T$, an empty standard cover, and the case $T$ nonaffine: the latter shows why the affine subsite has no final object in general and why a naive finite-limits proof of exactness would be invalid. Step 4 instead uses full-site exactness and the affine/full topos equivalences. I corrected the source label of 03Q1 after reading the TeX.

## Unfinished

No proof step is left unfinished. The new 03Q1 node is intentionally unsplit for the queue. Its source file is wanted in the project's literature tree, although its text was available for this review from the official Stacks page and the read-only local copy.
