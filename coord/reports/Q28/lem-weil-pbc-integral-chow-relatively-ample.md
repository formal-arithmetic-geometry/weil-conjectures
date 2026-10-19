## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-integral-chow-relatively-ample.json`: existing item copied from the repository, marked `split`, with its six proof steps and existing dependency route retained.
- `citations.json`: 26 verbatim statement citations, one for every dependency used by every proof step.
- No new DAG nodes were needed: every geometric, scheme-theoretic-image, projective-space, and module fact used by the proof already exists in the DAG.

## Attachments

The archived declaration `AlgebraicGeometry.exists_integral_chow_relatively_ample` has the exact item statement but its proof is `sorry`; it is therefore not an attachment. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item.

## WANTED

None.

## Problems found and corrections

The repository item was already a complete natural-language split, but was still marked `unsplit`; I retained its statement, dependencies, source places, blueprint ancestry, and six proof steps, and changed only the stage-1 status and split report for this Q28 delivery. The Lean metadata points to an archived theorem with a `sorry`, so it cannot close the item. No statement dispute, duplicate node, or missing dependency was found.

## Unfinished

No unfinished split work remains. The item still depends on the existing unsplit/split DAG nodes listed in its `proof_deps`; this delivery creates no additional nodes.

## Review by Q28

I read the item node, `dag/units/sk-thm-p1.json`, `dag/chapters/sec-proper-base-change.json`, the ancestor blueprint node `lemma-weil-pbc-smooth-curve-artin-schreier`, and the source passages in `literature/stacks-project/coherent.tex` (Tags 0200 and 0201), `morphisms.tex` (Tag 02NR), `properties.tex` (Tag 01PU), and `etale-cohomology.tex` (Tag 0A3M). The item statement agrees with the source route: a field base, an integral separated finite-type scheme without properness, a proper surjective Chow modification that is an isomorphism on a nonempty open, an immersion into projective space over the field, and the pullback of the projective twist relatively ample on every affine inverse image.

Step 1 uses the statements of `lem-weil-pbc-finite-type-over-noetherian` and `lem-weil-pbc-chow-noetherian` exactly for Noetherianity and the Chow modification, together with the definitions of integral, proper, and finite type. I checked that `Spec k` is Noetherian for a field, that the two finite-type hypotheses are present, and that integrality supplies nonemptiness so the chosen open can be nonempty. The finite-type composition argument is the elementary affine-local argument described in the step.

Step 2 uses `lem-weil-pbc-locally-noetherian-quasi-separated` and `lem-weil-pbc-qcqs-morphism-permanence` for the quasi-compact, quasi-separated open immersion, `lemma-nagata-scheme-image-ideal-qc` for the scheme-theoretic image and closure, `lemma-nagata-scheme-image-restrict-open` for restriction to the open, and `def-nagata-scheme-theoretic-image` for the construction. I verified that the chosen open is affine, that the image theorem applies to the resulting quasi-compact morphism, and that the restriction of the identity has zero kernel, giving the asserted isomorphism over the open.

Step 3 uses `lem-weil-pbc-scheme-image-qc-kernel` for the affine kernel description, `lem-sc-integral-scheme-stalks-in-function-field` for domain stalks and injectivity into the function field, and `def-pc-integral-scheme` for the reduced-plus-irreducible characterization. I checked the nilpotent argument on each affine chart: a nilpotent section restricts to zero in every integral stalk, hence lies in the image kernel; the closure of the irreducible dense open is irreducible. This is the explicit reducedness argument required by Remark 0201(3), rather than an unsupported claim that every Chow modification is integral.

Step 4 uses `lem-weil-pbc-proper-fp-permanence` for properness, base-change permanence, and composition of immersion/separated/finite-type properties, with `def-weil-proper-morphism` and `def-weil-finite-type-morphism` supplying the definitions. I checked that the composite image is closed by universal closedness and contains the nonempty dense open, hence is all of X; that the closed immersion c makes π proper; and that j and the structure map have the required k-compatibility and finite-type/separated properties.

Step 5 uses `lem-chow-tuple-immersion` for the graph map into `P^N_X`, `def-nagata-projective-space-base-change` to identify the fibre product, `lemma-nagata-projective-space-base-change-proper` for the projective projection, `def-weil-proper-morphism` for separatedness of that projection, `lem-weil-pbc-proper-over-separated` to make the graph map proper, and `lem-weil-pbc-proper-immersion-closed` to turn a proper immersion into a closed immersion. I checked that the graph is over X, that only π is required proper, and that no properness of X over k was silently introduced.

Step 6 uses `def-pc-projective-space-twist` and `def-pc-module-pullback` for the twist and pullback, `lem-weil-pbc-projective-space-standard-charts` for the standard-chart generators and their overlap relations, `lem-weil-pbc-proper-fp-permanence` for base-changing the graph closed immersion, and `lem-weil-pbc-projective-ample-invertible` for invertibility and ampleness on each affine base change. I checked the identification of the field projective twist with the pullback from the integral Proj model, the equality of the two projections, and the restriction to every affine W, including the empty affine open where the conditions are vacuous. The finite coordinate set is nonempty because N+1 is positive, and N=0 remains allowed.

I searched the full DAG and blueprint for the item and for every prospective dependency before deciding that no new node was warranted; the existing nodes state all cited facts. I also reran the required Q28 Mathlib searches for the unchanged item statement: LeanFinder and LeanSearch returned only normalization/integral-morphism generalities, Loogle returned no matching declaration, and the Mathlib grep returned only author-name false positives. Thus the item is not a Mathlib leaf and the existing natural-language proof is the appropriate split.
