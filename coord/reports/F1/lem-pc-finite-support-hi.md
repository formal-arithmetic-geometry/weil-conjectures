# Stage 1 report

1. Files written: `dag/nodes/sec-picard-framework/lem-pc-finite-support-hi.json` (item only; no new nodes). `citations.json` records the verbatim statement portions used by each proof step.
2. Attachments: none. The target declaration `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_of_isPullback` in `WeilConjectures/AlgebraicGeometry/Cohomology/Projective.lean:55-73` contains `sorry`.
3. WANTED: none.
4. The returned clause-shaped children were dropped. The proof now uses the existing open-restriction, affine direct-image, affine vanishing, Mayer--Vietoris, higher-direct-image presheaf, induction, and quasi-coherent extension nodes. Step 1 proves quasi-coherence by affine restriction and qcqs open induction. Step 2 defines the induction property with every affine base change quantified and obtains the union bound by max-plus-one Mayer--Vietoris gluing. Step 3 takes a finite affine cover of the base and then affine opens after arbitrary base change. Step 4 cites the presheaf identification so vanishing on an affine basis implies vanishing of the higher direct-image sheaf. The unsupported claim that induction data can simply be pulled back was removed, as was the duplicate open-restriction statement.
5. No unfinished work remains in the split.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by F1

I checked the item against Lean `exists_isZero_higherDirectImage_of_isPullback` and Stacks Tag 01XJ; its qcqs hypotheses, quasi-coherence clause, uniform bound, and arbitrary-base-change clause agree. I opened every cited node and verified that its statement supplies the fact used in the corresponding step: open restriction in Step 1, affine direct-image and affine cohomology vanishing on affine opens, the Mayer--Vietoris long exact sequence for the gluing, the induction principle, the quasi-coherent extension statement, and the cohomology presheaf description in Step 4. The kernel/cokernel passage in Step 1 is the elementary affine-local check from the quasi-coherence definition. For Step 2 I checked that the property quantifies over every affine `S' -> S`, that affine base change of an affine open is affine, and that unions and overlaps base change to unions and overlaps. For Step 3 I checked the finite affine cover and the map of each affine open of `S'` into a member of that cover. The final step uses the cited presheaf statement, rather than calling this identification a definition. Quasi-separatedness is used only for quasi-compact overlaps; no affine-intersection claim is made.

## Second reading by F1

- Statement: checked against `coherent.tex`, Lemma 30.4.5, Tag 01XJ, clauses (1)--(3), hypothesis by hypothesis; the base-change objects and arbitrary quasi-coherent sheaf are now explicit.
- Step 1: checked against Tag 01XJ clause (1) and each cited node statement; affine-local reduction, induction, Mayer--Vietoris, and extension closure are supplied.
- Step 2: checked against the finite-affine-cover induction in Tag 01XJ; the property quantifies over arbitrary affine base changes and the Mayer--Vietoris bound is applied after base change.
- Step 3: checked against Tag 01XJ clause (3); finite affine covers of the base and affine opens after arbitrary base change give the common bound.
- Step 4: checked against the actual stalk-colimit isomorphism stated by `lem-weil-pbc-higher-direct-image-presheaf`; vanishing on affine neighborhoods forces every stalk to vanish.
- D2 repaired: both clause-shaped child nodes were removed; the clauses are carried by the item's proof steps.
- B3 repaired: the duplicated open-restriction statement was removed with its child.
- C1 repaired: Step 2 now cites `lem-sc-mayer-vietoris-open-cover` for the long exact sequence.
- E/D repaired: Step 2 defines the full base-change-stable property, and Step 3 explicitly takes finite affine-cover maxima and affine opens after base change.
- C1 repaired: Step 4 cites `lem-weil-pbc-higher-direct-image-presheaf` for the identification of higher direct images with the cohomology presheaf.
- C4 repaired: Step 4 now uses the cited node's stalk isomorphism, rather than claiming an unstated associated-sheaf identification.
- B2/E repaired: the item statement now introduces $X'$, $g'$, $f'$, and arbitrary $\\mathcal F'$ for the base-change clause, matching Tag 01XJ.
