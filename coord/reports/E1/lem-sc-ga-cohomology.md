# lem-sc-ga-cohomology

## Worker result

- Updated `dag/nodes/sec-curve-estimates/lem-sc-ga-cohomology.json`: split the comparison and vanishing argument into three steps. Its statement now names the curve, quasi-coherent module, two cohomology theories, and the additive etale sheaf explicitly. The comparison uses the existing `lem-sc-etale-zariski-qcoh-comparison` (Stacks 03DW); the vanishing uses the new node below (Stacks 02UZ). The finite-type-to-Noetherian step cites the existing Mathlib leaf `lem-weil-pbc-finite-type-over-noetherian`.
- Added `dag/nodes/sec-curve-estimates/lem-sc-noetherian-cohomology-above-dimension.json`, an unsplit statement: on a Noetherian scheme, quasi-coherent Zariski cohomology vanishes above the topological dimension. Mathlib search verdict: no match. Stacks Cohomology Proposition 02UZ proves the stronger assertion for every abelian sheaf on a Noetherian topological space. Its proof inducts on dimension and irreducible components; on an irreducible space it reduces to extension by zero of a constant sheaf on an open and uses the lower-dimensional closed complement. This is a genuine input to the item, not a restatement of its etale comparison.

## Lean attachment

`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt` belongs to `lem-sc-noetherian-cohomology-above-dimension`; **has sorry** in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/AlgebraicGeometry/Cohomology/EulerChar.lean:64-73`. The declaration is recorded in the new node's `lean_audit.slopmaster2.decls`. No exact sorry-free declaration for the item was found; `WeilConjectures/AlgebraicGeometry/Sites/ArtinSchreier.lean:22-27` says the etale/Zariski quasi-coherent comparison is not yet available there.

## Source and edge checks

Stacks Descent Proposition 03DW (`descent.tex`, label `proposition-same-cohomology-quasi-coherent`, part 2) applies to any scheme and quasi-coherent module, hence to every curve here. Stacks Cohomology Proposition 02UZ (`cohomology.tex`, label `proposition-vanishing-Noetherian`) requires a Noetherian topological space and a degree strictly above its dimension; a finite-type curve over a field is Noetherian and has dimension at most one. For an empty curve the dimension is bottom, and for a zero-dimensional curve every positive degree vanishes as well. Taking the module to be `O_C` gives the additive sheaf `G_a` sectionwise.

The imported second step chose two points only in a compactification and then treated `C` minus each point as a proper open of that compactification. If a chosen point lies outside `C`, that open is just `C`, so this does not prove affineness. The source-based dimension argument avoids this gap.

## Checks

`tools/review_split.py lem-sc-ga-cohomology`: PASS, one new node. `tools/blueprint_refs.py check lem-sc-ga-cohomology`: zero field errors. `tools/check_dag.py`: no cycles or self-loops; it reports seven reach and eleven route errors in other nodes already present at the fetched base, none involving this item.

## Open work

The new Stacks 02UZ node remains unsplit; the matching Lean theorem contains `sorry`. No Lean was written or built.

## Review by E1

I read Stacks Descent Proposition 03DW in `descent.tex` and Cohomology Proposition 02UZ in `cohomology.tex`, then compared them with both node statements. The item assumes a curve over an algebraically closed field, hence a scheme and quasi-coherent module of the kind 03DW treats; 03DW(2) gives the canonical etale/Zariski cohomology isomorphism in every degree. The new node assumes a Noetherian scheme, a quasi-coherent module and a degree above its topological dimension. These are a specialization of 02UZ, which treats every abelian sheaf on a Noetherian topological space. Its statement includes the empty space: 02UZ's dimension bound is vacuous there, and all cohomology groups vanish.

In step 1, `lem-sc-etale-zariski-qcoh-comparison` states exactly the required isomorphism for any scheme; inversion changes only its direction. In step 2, `def-sc-curves` supplies finite type over a field and dimension at most one, `lem-weil-pbc-finite-type-over-noetherian` supplies Noetherianity because a field is Noetherian, and the new 02UZ node supplies vanishing for every `q >= 2`. In step 3, `def-sc-etale-qcoherent-module` identifies the associated structure-sheaf sections with the additive sheaf's sections, and the two comparison/vanishing nodes give the displayed conclusion. No step uses a fact hidden in a cited node's proof.

For the new unsplit node I searched the DAG for 02UZ, Grothendieck vanishing, and dimension-bounded cohomology, including the narrower projective-curve node `lem-pc-vanishing-above-dim`. I searched the full imported blueprint with `tools/blueprint_refs.py search`, with no exact blueprint node found. LeanSearch, LeanFinder, Loogle and available source grep are recorded in its `mathlib_searches`; no Mathlib declaration states the vanishing. The source checkout has the corresponding theorem `Modules.subsingleton_H_of_topologicalKrullDim_lt` in `EulerChar.lean:64-73`, but its body is `sorry`, so the node remains unsplit. The node introduces its own scheme, module, degree, dimension and cohomology, and cites each definition. The intended argument is recorded above under Worker result; it is not an empty renaming of the item.

I checked the hypotheses at their uses: finite type over a field in step 2 is sufficient for Noetherianity; dimension at most one makes `q >= 2` strictly above it; 03DW needs no smoothness or connectedness, so using it on a smooth connected curve is valid. Tests on a smooth affine curve, smooth proper curve, a disconnected curve, a zero-dimensional curve, and the empty curve give the same bound. I replaced the imported compactification proof because it chose points outside `C` without ensuring that the resulting opens of `C` were proper opens of the compactification. No source or statement was weakened.
