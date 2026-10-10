1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-cech-resolution.json`: split item; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-derived-acyclic-resolution.json`: statement-only supporting node; no Mathlib match.
- `citations.json`: verbatim citations for steps 2 and 3.

2. Attachments: none.

3. WANTED: none.

4. The imported proof had the right three-part route but omitted citations for the separated affine-intersection fact and for the final acyclic-resolution computation. I reused the existing `lem-weil-pbc-separated-affine-open-intersection`, `lem-pc-affine-morphism-hi`, and `lem-pc-affine-vanishing` nodes, and added the missing generic statement-only derived-functor node. The local contracting-homotopy step is elementary and is marked as such. No statement change was made.

## Review by H1

I read the item node and its blueprint proof, and checked the existing affine-intersection node in `sec-proper-base-change`: it explicitly states that affine opens of a separated morphism over an affine base have affine intersection, including the finite-union consequence used here. I read `lem-pc-affine-morphism-hi` and verified that it supplies vanishing of all higher direct images for each affine `j_J`, and read `lem-pc-affine-vanishing` to verify the affine-base cohomology vanishing used in the Leray calculation. Step 1 uses only restriction to a member of the cover and the insertion contracting homotopy, so it is marked elementary. Step 2 cites exactly those three statements and checks the hypotheses: `X -> Spec(A)` is separated, each `U_J` and its intersections are affine, and `F` remains quasi-coherent on restrictions. Step 3 cites the new node, whose statement explicitly takes an exact augmented finite resolution with every term acyclic and identifies the resulting cohomology with the right derived functors. I tested the supporting criterion on the one-term resolution `0 -> M -> C^0 -> 0` and on the identity functor, where it reduces to ordinary exactness. Mathlib searches were run for the item and supporting node; LeanSearch was unavailable and recorded as such, while LeanFinder/Loogle/grep returned only general infrastructure or no match.

## Second reading by H1

- Item statement: checked the separated quasi-compact morphism, finite affine cover, alternating augmented Cech complex, and acyclicity conclusion against the blueprint node and its three proof paragraphs; verdict: hypotheses and conclusion agree.
- Step 1: checked local restriction and the insertion contracting homotopy; verdict: elementary and sufficient for sheaf exactness.
- Step 2: checked citations `lem-weil-pbc-separated-affine-open-intersection`, `lem-pc-affine-morphism-hi`, and `lem-pc-affine-vanishing` verbatim; verdict: each cited statement supplies the claimed affine-intersection or vanishing fact under the stated hypotheses.
- Step 3: checked the finite acyclic-resolution argument against the new supporting statement and Stacks Proposition 13.16.8 (Tag 05TA); verdict: the resolution criterion gives the asserted derived direct image computation.
- Supporting node `lem-pc-derived-acyclic-resolution`: checked self-contained abelian-category, left-exact additive functor, enough-injectives, exact augmented finite resolution, and acyclicity hypotheses; verdict: statement-only, no duplicate node found, and the one-term and identity-functor edge cases reduce correctly.
- Mathlib searches: checked the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch entries in `searches.jsonl`; verdict: no exact Mathlib declaration for either statement.

Changes: corrected the supporting node source to Stacks Proposition 13.16.8 (Tag 05TA), and added this second-reading audit. No mathematical statement or proof step was weakened.

## Not duplicates

- `lem-pc-derived-acyclic-resolution` vs `lem-sp-derived-functor-single-identification` (05TA): the existing node identifies the cohomology of `Rv(X[0])` with classical `R^p v(X)` for one object via an injective resolution; this node states the distinct acyclic-resolution computation for an arbitrary finite augmented resolution and the cohomology of its termwise `v`-image.
- `lem-pc-derived-acyclic-resolution` vs `lem-weil-pbc-leray-acyclicity-quasi-iso` (05TA): the existing node proves that applying a left exact functor preserves quasi-isomorphisms between bounded-below complexes of acyclic terms; this node computes `R^q v(M)` directly from one exact augmented finite resolution and does not assert preservation of a quasi-isomorphism.
