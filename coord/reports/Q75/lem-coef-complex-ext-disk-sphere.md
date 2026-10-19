# Worker report: lem-coef-complex-ext-disk-sphere

## Files written

- `dag/nodes/sec-six-functors/lem-coef-complex-ext-disk-sphere.json`: existing item audited and marked `split`; no new nodes.
- `citations.json`: verbatim statement quotes for all cited nodes in all proof steps.
- `report.md`: this report.

## Attachments

No exact sorry-free declaration in `WeilConjectures/` states this item. The source checkout has no declaration tagged `(blueprint: lem-coef-complex-ext-disk-sphere)`.

## WANTED

WANTED: Gillespie, *The flat model structure on Ch(R)* (2004), Lemma 3.1 and the degreewise split extension discussion preceding Proposition 3.6, for the disk/sphere and degreewise-split calculations. The proof below is therefore recorded as agent-written from the explicit abelian-category constructions.

## Existing nodes and Mathlib searches

The proof uses the existing nodes `def-sp-abelian`, `def-sp-injective-resolutions`, `lem-weil-pbc-cochain-complexes-degreewise-exact`, `lem-weil-pbc-pushout-short-exact-sequence`, `lem-weil-pbc-snake-lemma-abelian`, `lem-sp-abelian-refinements`, and `lem-weil-pbc-abelian-exact-epi-cokernel`; I opened each statement before retaining the citation. No new node was necessary. The recorded searches were rerun with the item id: LeanFinder for Yoneda Ext on disks/spheres and for degreewise-split classification, Loogle for `Ext, CochainComplex`, grep for degreewise-split/cocycle/disk/sphere/HomComplex in `Algebra/Homology`, and LeanSearch for Ext to an injective single-term complex. Mathlib provides cocycle construction and resolution-based Ext equivalences, but no classification of arbitrary Yoneda extensions by disks, spheres, or Hom-complex cohomology, so the item remains a non-Mathlib split statement.

## Review by Q75

I read the item, its chapter and unit records, and the current blueprint proof of `prop-coef-integral-exceptional-adjoint`. The blueprint says these are auxiliary agent-formulated building blocks and requests Gillespie; it does not state a competing disk/sphere theorem. I also searched the source checkout for the exact blueprint tag and theorem names and found no attachment.

Step 1 uses only the cited statements that complexes form an abelian category, pushouts preserve short exact sequences, the snake comparison gives an isomorphism when endpoint maps are identities, and epimorphic refinements characterize exactness. It explicitly constructs the pullback/pushout interchange map and checks the endpoint maps. Steps 2–3 construct and invert the first disk correspondence by a pushout and the endpoint comparison. Step 4 applies the stated abelian-category duality operation and tracks the index to obtain the second disk formula.

Steps 5–7 construct and invert the sphere correspondence. I checked the acyclicity hypothesis exactly where it is used to make `Y^n → Z^(n+1)Y` epimorphic, and checked the dual sphere calculation uses the exact-epi-cokernel node to identify the cycle object with `Z^(n+1)X`. Steps 8–9 verify the split-extension/Hom-complex classification: the zero Yoneda class is the split extension, degreewise splittings produce the off-diagonal cocycle, changing splittings changes it by a coboundary, and every cocycle gives a square-zero differential. Step 10 verifies Baer additivity and naturality by the same pushout/pullback endpoint comparisons; the direct-sum and diagonal/addition calculations are written explicitly. Step 11 uses injectivity only to split component extensions and extend maps across monomorphisms; it computes the cocycle quotient as `Hom(H^(n-1)(X), I)` without assuming `X` acyclic.

I checked the edge cases of zero objects, arbitrary integer indices, non-acyclic `X` in the final injective clause, and the absence of projective or concrete-element assumptions. I checked every `uses` entry against the cited node's statement and generated `citations.json` with verbatim quotes. The only correction to the imported record was changing its stale `status` from `unsplit` to `split` and refreshing the split audit; no statement, hypothesis, dependency, or proof clause was weakened.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.
