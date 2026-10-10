# Stage 1 report: lem-weil-pbc-pullback-finite-locally-constant

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-pbc-pullback-finite-locally-constant.json`: item split into three proof steps; no new nodes.
- `citations.json`: verbatim citations for every node used by every step.

## Attachments

None. The source declaration `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.upperStar` proves only the preservation clause in the newer source API and does not state the full etale-site composition isomorphism in the item, so it is not an attachment for this item.

## WANTED

None.

## Review by J1

I read the item against Stacks Etale Cohomology Lemma 095A (label `lemma-pullback-locally-constant`, line 9960), the cited stalk result Lemma 03Q1 (3), and Sites Lemma 03CB for composition of morphisms of sites. The hypotheses are unchanged: `f : Y -> T` and `g : Y' -> Y` are scheme morphisms, `F` is an abelian sheaf on `T_Et`, and `f^{-1}F` is finite locally constant on `Y_Et`.

Step 1 uses the existing node `lem-weil-pbc-site-morphism-composition`, whose statement explicitly gives the inverse-image isomorphism for a composite morphism of sites. This supplies exactly `(f o g)^-1 F ~= g^-1(f^-1 F)` after matching the node's `u,v` to `f,g`.

Step 2 uses `lem-weil-pbc-etale-base-change-finite-limits` for the fact that each member of a trivialising etale cover remains etale after base change, and uses `def-weil-pbc-etale-sheaves` for the definition of finite locally constant as locally constant plus finite geometric stalks. The constant-sheaf pullback assertion is checked directly from the defining presheaf: every object receives the same coefficient group, so restriction remains constant. The node `lem-weil-pbc-inverse-image-stalk-germ` states the required canonical stalk isomorphism, so finite stalks transfer along `g`. The same composition node identifies the restriction to the pulled-back cover with the required iterated inverse image. No unstated hypothesis such as quasi-compactness or separatedness is used.

Step 3 is the elementary combination of Steps 1 and 2 and restates the two conclusions of 095A. The small edge cases were checked: an empty or singleton trivialising cover is still handled, and a finite stalk remains finite under the displayed bijection.

I searched the whole DAG and blueprint for 095A, 03Q1, 03CB, and the keywords “finite locally constant pullback”; the relevant composition, base-change, and stalk nodes above already exist, so no duplicate node was created. Mathlib searches were run with LeanSearch (unavailable), LeanFinder, Loogle, and grep; none supplies the small-etale theorem. The imported one-line Mathlib grep search was retained, and the new searches are recorded in the node.

## What was wrong or corrected

The imported item had no proof and only a single Mathlib grep search. I supplied the source-traceable proof, complete proof dependencies, all required Mathlib search records, and the citation file. No statement or hypothesis was changed.

## What remains unfinished

Nothing for this stage; the item is ready for the second reader.

## Second reading by J1

- Item statement: checked against Etale Cohomology Lemma 095A (`lemma-pullback-locally-constant`) and the inverse-image/stalk formulation of 03Q1(3); hypotheses and composite conclusion agree, including zero and singleton-cover cases.
- Step 1: checked against the statement of `lem-weil-pbc-inverse-image-composition`; it gives the scheme-morphism inverse-image isomorphism used here.
- Step 2: checked against `def-weil-pbc-etale-sheaves`, `lem-weil-pbc-etale-covering-base-change`, `lem-weil-pbc-inverse-image-stalk-germ`, and `lem-weil-pbc-inverse-image-composition`; each cited statement supplies the asserted finite-stalk, covering, stalk, or composition fact.
- Step 3: checked as an elementary combination of Steps 1 and 2 and the item conclusion.
- New nodes: none; duplicate search found the specialized inverse-image-composition node and the existing etale-cover base-change node.
- Changed Step 1 and Step 3 to cite the existing scheme-specific inverse-image-composition node instead of the generic site-composition node.
- Changed Step 2 and `proof_deps` to cite the existing etale-covering base-change node, which explicitly supplies joint surjectivity after base change.
- Repaired `citations.json` with verbatim statements for all revised dependencies.
