## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-quasi-finite.json` — statement, split proof, and corrected main-20261015 blueprint reference.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-finite-pushforward-punctual.json` — new unsplit statement node; Mathlib searches found no match.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-extension-by-zero-punctual.json` — new unsplit statement node; Mathlib searches found no match.

## Attachments

- `AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite` and the two weight declarations are sorry-bearing in slopmaster2 and therefore are not attachments.
- `lem-zl-finite-adic-direct-image` is an existing unsplit tool node supplying rational finite direct-image exactness and stalks.

## WANTED

None.

## Source and statement review

The item statement and proof were compared with `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-quasifinite/lem-zl-quasi-finite.md` and its `.proof.md`. The imported older statement was replaced by the current three-clause statement: vanishing of higher $R^ig_!$, preservation of mixed upper weights, and preservation of punctual upper bounds. The finite-field, finite-type, separatedness, quasi-finiteness, quasi-separatedness, constructibility, coefficient, and weight hypotheses were retained exactly.

The first item step uses the existing Zariski-main factorization node, whose statement supplies a quasi-compact open immersion followed by a finite map, and the functor-package node, whose third clause supplies compact-support composition and the proper equality $Rf_!=Rf_*$. The hypotheses match because finite-type schemes over the finite field are quasi-compact and the target is assumed quasi-separated. The second step uses the new extension-by-zero exactness statement and the existing rational finite direct-image exactness statement, so the factorized derived image is concentrated in degree zero. The third step uses the two new preservation statements: extension by zero leaves the local Frobenius stalk unchanged or zero, while finite pushforward preserves the local eigenvalue bound. The fourth step uses the verbatim filtration definition of mixedness; exactness transports the filtration and the two preservation lemmas keep every pure graded quotient pure. Every citation was checked against the cited node statement and recorded verbatim in `citations.json`.

For the finite-pushforward node I read `lem-a1-finite-map-purity.proof.md`, the existing finite rational direct-image node, and `lem-a1-finite-weil-sections-decomposition`. Its hypotheses are finite morphism, constructible Weil sheaf, and the same finite-field coefficient datum. The eigenvector argument does not assume semisimplicity: a nonzero block component gives $\\lambda^e=\\alpha$, and $q_x=q_y^e$ yields the absolute-value relation. I checked degree-one and degree-two finite field fibres, zero stalks, and a non-diagonalizable Frobenius block. For the extension node I read the extension-by-zero definition and the item proof paragraph: the presheaf is input-valued on objects factoring through the open and zero elsewhere, so exactness and the stalk/Frobenius claim follow objectwise and after sheafification; the empty-complement and empty-sheaf cases are vacuous.

## Review by NX

I opened the current item, both new nodes, every node cited by every proof step, the unit record, and the current blueprint proof. Step 1 takes exactly the factorization and composition/properness statements cited. Step 2 takes exactness from the extension node and from the rational finite-direct-image node; no finite-étale hypothesis is introduced. Step 3 takes only the upper Frobenius bound stated by the two preservation nodes. Step 4 takes the explicit finite filtration and pure quotient condition from `def-weil-punctual-weights`, then applies exactness and the two purity-preservation conclusions. The finite-pushforward node's Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch (with a second phrasing); the extension node was searched with the same required search families. No duplicate blueprint or DAG statement was found. The only off-unit citation is the existing finite rational direct-image tool, declared in the item's `tool_uses` because this unit has no equivalent generic exactness/stalk theorem. No SGA source was used.
