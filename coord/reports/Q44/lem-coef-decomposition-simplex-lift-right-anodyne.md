## Worker report

The item module states the simplex-lift criterion from HTT Proposition 4.2.3.8. It uses
`K : SSet.{u}`, `I : Type u` with `[Category.{u} I]`, and
`F : I ⥤ Over K`; `SimplexLiftObj` is the pair consisting of an index and an
`m`-simplex in its source over `z`, and `SimplexLiftHom` is an arrow of `I` carrying
one lift to the other. `simplexLiftCategory` supplies the ordinary lift category.
`SimplexLiftDegenerate` is the Mathlib degenerate-simplex predicate on the lift and
`simplexLiftDegenerateInclusion` is the full-subcategory inclusion. The module defines
`pureUpperSimplex`, its degreewise natural map `pureUpperNerveMap`, and
`decompositionNerveInclusion` into the recorded `localColimitDecomposition F`.
The theorem `rightAnodyneExtensions_decompositionNerveInclusion` has the two source
hypotheses and the right-anodyne conclusion; its proof is postponed with `sorry`.

The unique nondegenerate decomposition used in the proof is already supplied by the
Mathlib declarations recorded by `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`:
`SSet.exists_nonDegenerate`, `SSet.unique_nonDegenerate_dim`,
`SSet.unique_nonDegenerate_simplex`, and `SSet.unique_nonDegenerate_map`. No private
replacement module is delivered.

The searches found no existing declaration of the HTT criterion, the lift-category
objects, or the canonical map in Mathlib, `WeilConjectures`, or `lean/Sheaf`.
LeanSearch queried “contractible simplex lifting categories degenerate subcategory weak
equivalence right anodyne”; Loogle/LeanFinder queried “right anodyne decomposition nerve”
and “simplicial sets over a fixed base with weakly contractible lift nerves”; grep searched
`rightAnodyne|right_anodyne|RightAnodyne|decomposition|I_sigma|liftCategory` in
Mathlib, `WeilConjectures`, and `lean/Sheaf`. The exact criterion and canonical map had
no matches; the Mathlib degenerate-simplex API was the exact dependency match.

## Second reading by Q44

I read the DAG node, HTT Notation 4.2.3.1 and 4.2.3.7, and Proposition 4.2.3.8,
then matched each item with the Lean declarations.

1. The node introduces a small simplicial set `K`; Lean has `K : SSet.{u}`.
   It introduces a small ordinary category `I`; Lean has `I : Type u` and
   `[Category.{u} I]`. It introduces a diagram `F : I → sSet_/K`; Lean has
   `F : I ⥤ Over K`, whose objects and arrows are exactly simplicial maps over `K`.
2. For `z ∈ K_m`, the node's `I_z` consists of `(a,w)` with
   `w ∈ (K_a)_m` and `π_a(w)=z`; Lean's `SimplexLiftObj F z` has fields `index`,
   `lift`, and `over` with exactly those types and equality. Its arrows are precisely
   the `u : a ⟶ b` satisfying `F(u)(w)=w'`, represented by `SimplexLiftHom.map`
   and `lift_map`; `simplexLiftCategory` gives the ordinary category.
3. The node's `D_z` is the full subcategory on degenerate lifts. Lean's
   `SimplexLiftDegenerate F z` uses `(F.obj x.index).left.degenerate m`, Mathlib's
   predicate for pullback along a noninjective surjective simplex operator, and
   `simplexLiftDegenerateInclusion` is `ObjectProperty.ι`, the full-subcategory
   inclusion.
4. The node's `K_F` is the decomposition simplicial set from
   `lem-coef-decomposition-local-colimit-cocones`; Lean uses
   `localColimitDecomposition F`. The pure-upper map is constructed from
   `orderedJoinInr`, the selected decomposition generator, the coproduct inclusion,
   and the coequalizer projection in `pureUpperSimplex`; the degreewise transports
   in `pureUpperNerveApp` handle arbitrary simplex-category objects, and
   `pureUpperNerveMap` is the resulting natural transformation. Thus
   `decompositionNerveInclusion F` is exactly the source inclusion `N(I) ⊆ K_F`.
5. The nondegenerate hypothesis is rendered as
   `∀ m z, z ∈ K.nonDegenerate m →
   Enhanced.IsContractible (nerve (SimplexLiftObj F z))`, where
   `Enhanced.IsContractible` is weak equivalence to the standard point, exactly
   “the nerve is weakly contractible.” The degenerate hypothesis is rendered as
   `∀ m z, z ∈ K.degenerate m → Enhanced.IsWeakHomotopyEquivalence
   (nerveMap (simplexLiftDegenerateInclusion F z))`, exactly the weak equivalence
   `N(D_z) ⊆ N(I_z)`.
6. The conclusion is exactly
   `rightAnodyneExtensions (decompositionNerveInclusion F)`, using the recorded
   right-anodyne morphism property. The theorem adds no quasicategory, poset,
   directedness, injectivity, finiteness, characteristic, or colimit hypothesis.

Edge cases were checked: empty `K` and empty `I` are permitted; then the quantified
hypotheses are vacuous and the canonical map is still defined. `m = 0` is included,
including degenerate and nondegenerate 0-simplices. Zero or empty source simplicial
sets are not excluded, and no universe below `u` is introduced. The source's
nondegenerate case automatically has an empty degenerate-lift subcategory, while the
separate degenerate condition covers exactly the remaining simplices.

One implementation mismatch was found and repaired: the retained attempt delivered a
new `SSet.exists_unique_nonDegenerate_decomposition` theorem and copied its DAG node,
even though that dependency is recorded as a Mathlib node with an exact four-declaration
match. I removed that duplicate module and copied node, and changed the item import to
`Mathlib.AlgebraicTopology.SimplicialSet.Degenerate`. The item statement, its `stmt_deps`,
its proof data, and all declarations above are otherwise unchanged.
