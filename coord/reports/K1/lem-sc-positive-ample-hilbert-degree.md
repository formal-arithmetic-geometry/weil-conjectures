1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-positive-ample-hilbert-degree.json`: repaired statement node with seven proof steps.
- `dag/nodes/sec-abelian-varieties/lem-sc-top-dimensional-reduction-intersection.json`: new unsplit statement node, no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sc-intersection-effective-cartier.json`: new unsplit statement node, no Mathlib match.
- `dag/nodes/sec-abelian-varieties/def-sc-intersection-number.json`: new unsplit definition node for Tag 0BEP, no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sc-proper-affine-finite-general.json`: Mathlib leaf matching `AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`.
- `citations.json`: verbatim statement quotes for every proof dependency.

2. Attachments: none.

3. WANTED: none.

4. What was wrong: the returned item still used a special finite-scheme node instead of the existing Tag 0AYT zero-dimensional support lemma, omitted ampleness of restrictions to top-dimensional components, used the wrong ampleness notion in step 4, and asserted the Hilbert-degree equality before establishing that the Hilbert polynomial has degree $g$. I removed the special node, cited `lem-pc-chi-zero-dim-support`, added the Tag 0893 restriction clause, argued step 4 directly from `def-sc-ample`, and made positivity imply `deg Q=g` before identifying the degree.

5. What could not be finished: no Lean proof was written at stage 1; the four new child statements remain unsplit as required.

## Review by K1

I read the full Tag 0BEV proof in `literature/stacks-project/varieties.tex`, Definition Tag 0BEP, and Tags 0AYT, 0BES, 0893, and 0BEU, plus the imported blueprint paragraph. Step 1 now uses the existing `lem-pc-chi-zero-dim-support` statement with $\mathcal F=\mathcal O_X$ and $\mathcal N=\mathcal L^{\otimes m}$; its support and nonempty global section hypotheses were checked. Step 2 explicitly carries restriction of ampleness to each top-dimensional component. Step 3 delays the degree equality until positivity forces the Hilbert polynomial to have degree exactly $g$. Step 4 argues directly from `def-sc-ample` via a very ample power and a projective coordinate, with no `def-weil-pbc-ample-invertible-module` citation. Steps 5--7 retain the checked finiteness, Cartier, and divisor-intersection arguments. I removed the duplicate special base node and repaired all corresponding citations and dependency lists.

For every cited node I opened its statement and copied only the sentence or formula used into `citations.json`; no step relies on a node's proof. I searched the whole DAG and blueprint for Tags 0AYT, 0BES, 0BEU, 01WN, 0BET, and 0BEP before creating children. The only existing 0AYT node is a different coherent-sheaf result, so the finite-scheme positivity base is stated separately; no existing node states the component reduction, Cartier intersection formula, or 0BEP definition. Mathlib searches were run for every new node with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. Edge cases checked were $g=0$, $X=\operatorname{Spec}k$, and positive-dimensional integral $X$ where proper plus affine would force finiteness. Section-number citations, the former one-step proof, and the missing 0BEP normalization citation were corrected.

## Not duplicates

lem-sc-intersection-effective-cartier vs lem-sc-positive-ample-hilbert-degree: the new node is the Cartier-divisor intersection equality used inside the induction; the existing item is the global positivity conclusion.
lem-sc-intersection-effective-cartier vs lem-sc-isogeny-facts: the new node is a general intersection formula; the existing node concerns multiplication isogenies and only cites positivity as an input.
lem-sc-proper-affine-finite-general vs lem-sc-positive-ample-hilbert-degree: the new node is the proper-plus-affine finiteness criterion; the existing item is positivity of an ample Hilbert degree.
lem-sc-proper-affine-finite-general vs lem-weil-pbc-finite-morphism-permanence: the existing node proves properties of an already finite morphism, while the new node derives finiteness from properness and affineness.
lem-sc-proper-affine-finite-general vs lem-weil-pbc-finite-closed-map-finite-fibres: the existing node starts with a finite morphism and derives closedness and finite fibres; the new node proves the converse criterion in the structure-morphism setting.
lem-sc-proper-affine-finite-general vs lem-weil-pbc-etale-splits-off-isolated-points-technical: the existing node uses finite-proper as one ingredient of an etale splitting argument; the new node states the proper-affine-to-finite implication.
lem-sc-proper-affine-finite-general vs lem-sc-isogeny-facts: the existing node's 0BEV citation is the isogeny argument's positivity input, while the new node is the independent proper-affine finiteness criterion.
lem-sc-top-dimensional-reduction-intersection vs lem-sc-positive-ample-hilbert-degree: the new node is the component decomposition sublemma; the existing item is the positivity theorem that uses it.
lem-sc-top-dimensional-reduction-intersection vs lem-sc-isogeny-facts: the new node concerns intersection numbers on components, while the existing node concerns isogeny degree identities.

## Second reading by K1

- Step 1 checked against Tag 0AYT via `lem-pc-chi-zero-dim-support`, including the support-dimension and positivity arguments.
- Step 2 checked against Tag 0BES and Tag 0893; the component formula now explicitly supplies ample restrictions.
- Step 3 checked against Definition Tag 0BEP, the Hilbert-polynomial node, and the Hilbert-degree definition; the degree equality is made only after positivity forces degree $g$.
- Step 4 checked directly against `def-sc-ample`; the projective-coordinate construction supplies a nonempty affine nonvanishing locus without the unrelated absolute-ampleness node.
- Step 5 checked against Mathlib `IsFinite.iff_isProper_and_isAffineHom` and the proper-affine argument: verdict sound after removing an unnecessary finite-type hypothesis from the leaf.
- Step 6 checked against the nonzero-section Cartier node and Tag 0BEU: verdict sound under the integral, proper, positive-dimensional hypotheses.
- Step 7 checked against the induction clause of Tag 0BEV and the Cartier-intersection node: verdict sound.
- `lem-sc-top-dimensional-reduction-intersection` checked against Tag 0BES and reducible/non-pure-dimensional examples: verdict repaired as stated above.
- `lem-sc-intersection-effective-cartier` checked against Tag 0BEU and a principal Cartier divisor: verdict sound.
- `def-sc-intersection-number` checked against Definition 0BEP: verdict sound for $Z=X$ and the $d=0$ case.
- `lem-sc-proper-affine-finite-general` checked against the Mathlib declaration and Tag 01WN: verdict repaired to the exact proper-plus-affine criterion.

Changes made: removed the pure-dimension restriction from the component node and updated its citation; corrected the ample-section tag in step 4; generalized the proper-affine Mathlib leaf and updated its citation. No node was removed.

## Second reading by K1

- Step 1 checked against Tag 0AYT and the existing zero-dimensional support node; the tensor-invariance and nonempty global-section arguments match.
- Step 2 checked against Tag 0BES, the component statement, and \`def-sc-ample\`; restriction ampleness is justified by composing the very-ample closed immersion with each component.
- Step 3 checked against Tags 0BEM/0BEP and the Hilbert-degree definition; the coefficient calculation and degree normalization are ordered after positivity.
- Step 4 checked against \`def-sc-ample\`; the chosen projective coordinate gives a nonempty affine principal open.
- Step 5 checked against Tag 01WN and the Mathlib proper-affine criterion; positive dimension excludes finiteness.
- Step 6 checked against the nonzero-section Cartier node and Tag 0BEU; the specialized intersection statement now carries its intersection-number definition dependency.
- Step 7 checked against the induction clause of Tag 0BEV and the Cartier-intersection statement; the restricted ample module supplies the induction hypothesis.
- \`lem-sc-top-dimensional-reduction-intersection\` checked for self-contained intersection-number terminology and reducible top-dimensional components; added \`def-sc-intersection-number\` as its statement dependency.
- \`lem-sc-intersection-effective-cartier\` checked against Tag 0BEU and principal Cartier divisors; added \`def-sc-intersection-number\` as its statement dependency.
- \`def-sc-intersection-number\` checked against Definition 0BEP, including the $g=0$ coefficient convention and the $X$ self-intersection specialization.
- \`lem-sc-proper-affine-finite-general\` checked against Mathlib \`IsFinite.iff_isProper_and_isAffineHom\` and Tag 01WN; exact criterion retained.

Changes made: added missing intersection-number definition dependencies to both Cartier/component child nodes; added the \`def-sc-ample\` citation to step 2; retained the four statement-only children and corrected the report to describe these repairs.
