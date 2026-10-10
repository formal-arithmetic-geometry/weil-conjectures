1. Files written:

- `dag/nodes/sec-abelian-varieties/pqf-lem-proper-basic.json`: statement split, no new nodes, Mathlib-backed dependency `lem-pc-separated-quasi-separated`.
- `citations.json`: verbatim step citations.

2. Attachments: none.

3. WANTED: none.

4. I found no sorry-free declaration tagged `pqf-lem-proper-basic` or stating the item exactly in `~/weil-src-slopmaster2/WeilConjectures`; the source grep found no project declaration for this lemma. The imported proof cited the broad conventions node and called the finite-type and separated-to-quasi-separated consequences without enough precision. I replaced that with the properness definition node and the existing node whose statement explicitly says separated implies quasi-separated. The item statement itself is unchanged.

## Review by C1

I read the blueprint node `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-pqf-finite/pqf-lem-proper-basic.md` and the Stacks definition of properness (Definition 29.41.1, Tag 01W1), together with the separatedness discussion in `schemes.tex` Section 01KH and Lemma 01K7. The first part of step 1 uses exactly the sentence in `def-weil-proper-morphism` defining proper as separated, finite type, and universally closed; the finite-type convention supplies quasi-compactness. The second part uses exactly the statement of `lem-pc-separated-quasi-separated`, which concludes that the diagonal is quasi-compact. The affine-base conclusion is an elementary specialization: the structure morphism is the given f, so its already proved separatedness and quasi-compactness are the asserted properties of X.

I opened both cited node files and checked their hypotheses: each concerns a morphism of schemes, and the item supplies such an f. I searched the DAG for duplicates by the item id, properness keywords, and the separated/quasi-separated statement; the latter existing node was reused rather than duplicated. I also ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; LeanFinder found `AlgebraicGeometry.isProper_iff` and `AlgebraicGeometry.IsSeparated.instQuasiSeparated`, while LeanSearch was unavailable and is recorded as such. The pinned Mathlib source confirms the corresponding declarations and the universal-closed-to-quasi-compact instance used by the definition match. Small cases checked were the identity of an affine scheme (all conclusions immediate), a proper closed immersion (separated and finite type), and the empty scheme over an affine base (the affine-base conclusion remains vacuous/true).

5. What I could not finish: nothing.

## Second reading by C1

- Step 1 checked against Stacks Definition 29.41.1 (Tag 01W1), the separated/quasi-separated paragraph after Definition 01KK and Lemma 01K7, and the cited node statements; verdict: correct after making the affine-base separatedness implication explicit.
- New nodes: none; the existing supporting nodes `def-weil-proper-morphism`, `lem-pc-separated-quasi-separated`, and `lem-sc-separated-over-affine-scheme-separated` were opened and their hypotheses match the step.
- Small cases checked: the identity of an affine scheme, a proper closed immersion, and the empty scheme over an affine base; all conclusions hold.
- Changed the proof and `proof_deps` to cite `lem-sc-separated-over-affine-scheme-separated` for “$S$ affine implies $X$ separated,” and added its verbatim statement to `citations.json`; this fixes the previously implicit transitivity/affine-base argument.
- Rechecked the existing-node search by item id and properness/separatedness keywords; no duplicate node was created. Mathlib search records were retained, including the unavailable LeanSearch result.
