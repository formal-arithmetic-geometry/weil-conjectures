## Worker report

The module `lean/Sheaf/AlgebraicGeometry/NoetherianBooleanAffineRefinement.lean`
states `AlgebraicGeometry.exists_noetherian_boolean_affine_refinement`. It introduces no
new definition: the finite family is indexed by `Fin r`, the given closed subschemes are
maps `i j : C j ⟶ X` with `[∀ j, IsClosedImmersion (i j)]`, and the affine Noetherian
hypotheses are `[IsAffine X] [CompactSpace X] [IsLocallyNoetherian X]`.

The conclusion is rendered clause by clause as follows. The witnesses `n`, `R : Fin n →
Scheme`, and `ι : ∀ α, R α ⟶ X` are the finite family of immersions. For each `α`,
`IsImmersion (ι α)` gives the immersion, `IsAffine (R α)` and `IsReduced (R α)` give the
affine reduced source, and `IsLocallyClosed (Set.range (ι α))` makes its image a locally
closed subset. `Pairwise (fun α β ↦ Disjoint (Set.range (ι α)) (Set.range (ι β)))` gives
pairwise disjoint images. `∀ x : X, ∃ α, x ∈ Set.range (ι α)` gives coverage of the
underlying space. For every `α` and `j`, the pullback is `pullback (i j) (ι α)` and its
projection to `R α` is `pullback.snd (i j) (ι α)`; the final disjunction says that its
underlying image is either `∅` or `Set.univ`.

The statement dependencies are used through the following recorded declarations:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` from `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace` from `Mathlib.Topology.Defs.Filter`.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian` from
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-weil-locally-closed-subset`: Mathlib `IsLocallyClosed`.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced` from
  `Mathlib.AlgebraicGeometry.Properties` (available through the imported scheme
  property modules).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`.

The proof plan is recorded in the declaration docstring. Its affine-partition input is the
existing `AlgebraicGeometry.Scheme.exists_partition_isImmersion_isAffine_isReduced` in
`WeilConjectures.AlgebraicGeometry.NoetherNormalization`, recorded by
`lem-zl-affine-partition`. The remaining proof dependencies are Mathlib declarations
recorded by their node `mathlib_match` fields: closed-immersion base change, the
pullback-image identity, Noetherian open-subscheme permanence, and immersion composition.

I checked the empty scheme and `r = 0`: the empty family is allowed. For `r > 0`, an
individual closed subscheme may itself be empty, and the final disjunction permits empty
pullbacks. A full pullback is represented by `Set.univ`; no nonemptiness hypothesis is
introduced. The finite output index is `Fin n`, so `n = 0` remains available for the empty
scheme. The source and all maps use one explicit universe `u`.

Searches performed:

- `msearch.py ... leanfinder "finite Boolean stratification of affine Noetherian scheme by reduced affine locally closed subschemes compatible with finitely many closed subschemes"`: eight hits about Noetherian schemes and affine covers; no matching Boolean refinement.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.exists_partition_isImmersion_isAffine_isReduced, AlgebraicGeometry.IsImmersion, AlgebraicGeometry.IsLocallyNoetherian"`: zero hits (the service reported the source declaration as an unknown identifier); no exact match.
- `msearch.py ... grep "closed.*subscheme.*partition|partition.*closed.*subscheme" Mathlib/AlgebraicGeometry`: zero hits.
- `rg` over `WeilConjectures/` for the item id, Boolean affine refinement, and finitely many closed subschemes: no exact declaration. The only relevant existing source declaration is the generic affine reduced partition used above, which does not encode compatibility with a prescribed finite family of closed subschemes.

The existing stage-1 split and Q30 review were read. The item statement and proof steps are
unchanged; this delivery only adds the stage-2 Lean record and declaration.

## Second reading by NG

I reread the item statement and matched every hypothesis and conclusion to the theorem.
`IsAffine`, `CompactSpace`, and `IsLocallyNoetherian` are exactly the affine and
Noetherian assumptions. `Fin r`, `C`, and `i` represent the finitely many closed
subschemes, with no positivity assumption on `r`. Each output clause is present: immersion,
locally closed image, affine and reduced source, pairwise disjoint images, coverage, and the
empty-or-full underlying pullback clause for every pair `(α,j)`. No extra geometric,
separation, or nonemptiness hypothesis was added, and no edge case was dropped.
