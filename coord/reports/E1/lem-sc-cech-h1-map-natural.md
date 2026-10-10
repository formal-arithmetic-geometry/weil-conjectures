# lem-sc-cech-h1-map-natural

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-cech-h1-map-natural.json`: split statement, 4 proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every proof citation.

## Attachments

None. The slopmaster2 audit says `none`; searches for the blueprint tag, Cech/H1 naturality, and nearby comparison declarations found no sorry-free declaration stating this item. `TopCat.Sheaf.nonempty_cechCohomologyFunctor_iso_functorH` concerns acyclic sheaves and is not a natural map for every module.

## Wanted

None. The checkout omits `literature/stacks-project/`, but the Stacks source was read from the machine's read-only copy at `/home/ubuntu/c1-stacks-review/cohomology.tex`, lines 1408-1480. The cited source path is the project's canonical literature path.

## Corrections and unfinished work

The imported item had no proof or Cech/module statement dependencies. I added the missing dependencies and expanded Stacks 01EQ's omitted functoriality check. The source's comparison is for a ringed space and an open subset; the item specializes to a scheme and the cover of the whole space. Nothing remains unfinished at this split level.

## Review by E1

I read Cohomology Lemma 01EQ (`lemma-cech-cohomology`) in `cohomology.tex`, including the complete displayed construction of alpha and beta, plus its cited injective Cech vanishing Lemma 01EP. The item's arbitrary sheaf of O_X-modules and arbitrary open cover match 01EQ; no affine or quasi-coherent hypothesis was inserted. The statement is degree one of the source's natural maps. No new nodes were created, so B1-B8 and small-case testing of new statements are vacuous. I searched the full DAG and blueprint for 01EQ, Cech comparison, injective Cech acyclicity and double-complex totalization; `lem-sc-cech-comparison-natural` is narrower (affine cover, quasi-coherent coefficients) and cannot replace this item. The adjacent Lean source has a Cech/sheaf comparison on acyclic classes, not the arbitrary-module map. The four-step proof tests correctly for the zero module (both maps zero) and a one-open cover (Cech H1 is zero); neither requires extra hypotheses.

Step 1 uses `lem-weil-pbc-scheme-modules-enough-injectives` to choose the resolution, `def-sp-injective-resolutions` for its shape, `def-weil-pbc-site-cech-complex` for termwise Cech maps, `def-sp-double-complex-total` for totalization, and `def-sc-zariski-site` for the open-cover sheaf condition. I checked each cited statement itself. The differentials kill the alpha and beta images by the sheaf and resolution axioms, an elementary check of the two square-zero identities. The source is 01EQ's first proof paragraph.

Step 2 uses the exact statement of `lem-weil-pbc-module-injective-open-cover-cech-acyclic`: higher Cech cohomology vanishes for an injective O_X-module and **any** Zariski open cover. `def-sc-zariski-site` gives gluing and uniqueness in degree zero. `thm-sp-double-complex-spectral-sequences` states convergence and functoriality for a first-quadrant double complex, and `def-sp-double-complex-total` defines its finite totalization. Each row is Cech of an injective term, so the row-first spectral sequence has only the zero column. Its edge map is alpha, making alpha a quasi-isomorphism. The hypotheses hold because the resolution is nonnegative and each term injective; no finite-cover condition is used.

Step 3 applies `pqf-def-cohomology`, whose statement defines H1 as derived global sections, and `lem-weil-pbc-derived-functor-map-via-lift`, whose statement identifies those groups and maps on a chosen injective resolution. `lem-weil-pbc-injective-resolution-lift-exists` supplies comparison maps for changes of resolution. Thus the inverse of alpha after beta yields the source's canonical comparison. These citations give the facts used; inversion of an isomorphism is elementary. I checked 01EQ's final paragraph where the same composite is specified.

Step 4 applies the **stated** lift theorem to an arbitrary module morphism, the **stated** Cech functoriality to get the horizontal cochain map, and the **stated** derived-functor map formula to identify the right side with H1(phi). The alpha square commutes by restriction; the beta square commutes by the lifting equation. Passing the two squares to cohomology gives the equation in the item. This writes out the functoriality that 01EQ explicitly omits. I found no hidden use of affine intersections, finite covers, or injectivity of the underlying abelian sheaf. The generic nodes filed in other units are declared as tool uses in `split_report`, because they provide homological machinery rather than a replacement route for the curve-estimate unit.
