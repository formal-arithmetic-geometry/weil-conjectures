Files written:

- `dag/nodes/sec-abelian-varieties/pqf-lem-pushforward-qcoh.json`: statement split; no new nodes; Mathlib search found only the affine special case.

Attachments: none.

WANTED: `literature/stacks-project/schemes.tex`, Schemes Lemma 01LC, for the exact source text (the repository contains the imported citation and Tag 01LC but not the Stacks checkout).

The source proof was checked against the imported Tag 01LC route. Step 1 reduces to an affine target, chooses a finite affine cover of the inverse image by quasi-compactness, and uses the existing Mathlib-backed node `lem-weil-pbc-quasi-separated-affine-cover-criterion` for quasi-compact pairwise intersections. The convention node supplies the qcqs hypotheses and `pqf-def-coherent` supplies the local associated-sheaf meaning. Step 2 is the sheaf equalizer for sections and is explicitly marked elementary. Step 3 applies the existing associated-sections localization node; exactness of localization and preservation of finite products are the elementary algebra used to identify kernels. Step 4 uses the definition of quasi-coherence on the principal-open basis. I verified every citation against the cited node statements and recorded verbatim quotes in `citations.json`. The cross-unit criterion is declared as a generic tool use because this unit has no replacement node. Small cases checked: an affine morphism (one affine in the cover), the identity morphism, and the empty scheme.

No statement or source clause was changed. No new node was created because the only non-elementary auxiliary fact needed, quasi-separatedness giving quasi-compact affine intersections, already exists as a Mathlib leaf.

## Review by C1

I read the imported item and the Tag 01LC proof route. Step 1 uses the conventions, quasi-coherent definition, and the existing affine-intersection criterion exactly as quoted; the qcqs hypotheses are present. Step 2 is the section sheaf equalizer and is elementary from the sheaf axiom. Step 3 uses the associated-sections localization statement and only elementary exactness of localization and finite products. Step 4 applies the quasi-coherence definition on principal opens. I corrected the imported proof by making the previously uncited affine-intersection fact explicit and by adding source locations, citations, blueprint metadata, and the declared tool use.

## Second reading by C1

- Item statement: checked against Schemes Lemma 26.24.1, Tag 01LC (the exact `lemma-push-forward-quasi-coherent` statement); the quasi-compact and quasi-separated hypotheses and the quasi-coherent conclusion agree.
- Step 1: checked against Tag 01LC, lines 4778--4784, and the statements of `def-weil-pbc-scheme-conventions`, `pqf-def-coherent`, and `lem-weil-pbc-quasi-separated-affine-cover-criterion`; finite affine covers and quasi-compact overlaps are justified under the stated hypotheses.
- Step 2: checked against the equalizer calculation in Tag 01LC, lines 4785--4793; the sheaf gluing argument is elementary for the finite affine cover.
- Step 3: checked against Tag 01LC, lines 4794--4812, and `pqf-lem-associated-sections-localize`; each affine section localizes, and exact localization plus preservation of finite products identifies the kernels.
- Step 4: checked against Tag 01LC, lines 4813--4819, and `pqf-def-coherent`; the principal-open identifications give the associated sheaf on each affine target.
- New nodes: none; there are no new statements to audit under B1--B7. The only auxiliary non-elementary fact is the existing Mathlib-backed affine-intersection criterion, searched and cited rather than duplicated.
- Edge cases: verified the affine morphism (one affine in the cover), identity morphism, empty scheme, zero module, and the cases $n=0$ and $n=1$ of the finite cover/equalizer construction.
- Changes: no mathematical or node changes were needed; this section records the source comparison, citation verification, blueprint/tool-use check, and edge-case audit.
