/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpace

/-! # Inverses and cover descent for shifted etale lines

Source: blueprint main-20261015, `thm-asd-smooth-tensor.proof.md`, paragraphs 2 and 4
(blueprint: lem-sf-shifted-etale-lines-locality).

The existing `IsShiftedRankOneLocalSystem` is exactly line shape: a shifted locally
constant module sheaf whose stalks at all separably closed geometric points are the ring.
Its existing `isInvertible`, `leftDerivedUpperStar`, `leftDerivedUpperStarShiftSingleIso`,
`tensor` and `of_jointlySurjective` declarations supply the corresponding clauses.
Here we state the additional inverse-shape clause and descent with the specified
cohomology sheaf. Cover indices may live in any universe; empty covers are allowed.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory AlgebraicGeometry.Scheme Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}

attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- A line of shape `n` has a two-sided derived tensor inverse of shape `-n`.

Source: blueprint main-20261015, `thm-asd-smooth-tensor.proof.md`, paragraph 2;
Stacks Tags 0B8Q, 0B8N, 03EO, 06YQ and 06YU
(blueprint: lem-sf-shifted-etale-lines-locality).

Proof: write `M ≅ L[n]`. On a trivializing etale cover `L` is constant with value `P`.
Discard empty members. At a geometric point of each remaining member, the constant-stalk
and inverse-image-stalk comparisons identify `P` with `A`. Thus `L` is locally free of
rank one over the constant ring sheaf. These trivializations pull back to a cover of
every object of the small etale site. The sheaf-line evaluation inverse-pair lemma gives
its dual `L^vee = Hom(L, A_X)`, locally free of rank one, and evaluation identifies both
orders of their tensor product with `A_X`. Both sheaves are flat. Conversely such local
trivializations imply locally constant and all separably closed stalks equal to `A`:
lift geometric points to the cover, and compare a separably closed point with its
algebraic closure by the geometric-point-field-extension lemma. The shifted single
complexes are bounded above and flat, hence K-flat. Their total tensor has its sole
nonzero term `L tensor L^vee` in degree zero, so `L^vee[-n]` is the desired inverse;
symmetry gives the opposite tensor order. The zero ring and empty scheme are allowed. -/
theorem exists_shiftedEtaleLine_inverse
    {M : DerivedCategoryModule A X} {n : ℤ} (hM : IsShiftedRankOneLocalSystem M n) :
    ∃ N : DerivedCategoryModule A X, IsShiftedRankOneLocalSystem N (-n) ∧
      Nonempty (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj N ≅
        constantComplex A X) ∧
      Nonempty (((derivedTensor (ModuleCat.{u + 1} A) X).obj N).obj M ≅
        constantComplex A X) := by
  classical
  obtain ⟨F, hF, hs, ⟨eM⟩⟩ := hM
  let D := (ihom F).obj (𝟙_ _)
  let eFD : F ⊗ D ≅ 𝟙_ _ := tensorIhomUnitIsoOfIsLocallyConstantSheaf F hs
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
  have (i : 𝒰.I₀) : AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
  let I := {i : 𝒰.I₀ // Nonempty (𝒰.X i)}
  let v (i : I) := 𝒰.f i.1
  have hv : ∀ x : X, ∃ (i : I) (y : 𝒰.X i.1), (v i).base y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩
  let eF (i : I) : ((v i)^*[ModuleCat.{u + 1} A]).obj F ≅ 𝟙_ _ := by
    have hc : (((v i)^*[ModuleCat.{u + 1} A]).obj F).IsConstant
        (𝒰.X i.1).smallEtaleTopology :=
      (isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i.1) F).1 (h𝒰 i.1)
    let t := (𝒰.X i.1).algClosurePoint i.2.some
    exact (nonempty_iso_unit_of_isConstant _ t
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) (v i) t).app F ≪≫
        (hs _ (t ≫ v i)).some)).some
  let eD (i : I) : ((v i)^*[ModuleCat.{u + 1} A]).obj D ≅ 𝟙_ _ :=
    (λ_ _).symm ≪≫ tensorIso (eF i).symm (Iso.refl _) ≪≫
      Functor.Monoidal.μIso ((v i)^*[ModuleCat.{u + 1} A]) F D ≪≫
      ((v i)^*[ModuleCat.{u + 1} A]).mapIso eFD ≪≫
      (Functor.Monoidal.εIso ((v i)^*[ModuleCat.{u + 1} A])).symm
  have hD : IsLocallyConstantSheaf D := by
    let (i : (etaleCoverOfJointlySurjective v hv).I₀) : IsLocallyConstantSheaf
        ((((etaleCoverOfJointlySurjective v hv).f i)^*[ModuleCat.{u + 1} A]).obj D) :=
      have := isLocallyConstantSheaf_unit (𝒰.X i.1) A
      IsLocallyConstantSheaf.of_iso (eD i).symm
    exact IsLocallyConstantSheaf.of_cover (etaleCoverOfJointlySurjective v hv) D
  have hsD : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale t).sheafFiber.obj D ≅ ModuleCat.of A A) := by
    intro Ω _ _ t
    obtain ⟨i, y, hy⟩ := hv (t.base (IsLocalRing.closedPoint _))
    obtain ⟨t', rfl⟩ := Scheme.exists_comp_eq_of_etale (v i) t ⟨y, hy⟩
    exact ⟨((upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) (v i) t').app D).symm ≪≫
      (pointSmallEtale t').sheafFiber.mapIso (eD i) ≪≫
      ((pointSmallEtale t').uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} A)).symm.app _ ≪≫
      sheafFiberUnitIso (ModuleCat.{u + 1} A) t'⟩
  let SF := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  let SD := (_root_.DerivedCategory.singleFunctor _ 0).obj D
  have hflat := ObjectProperty.flat_of_tensorIso eFD
  have hflatD := ObjectProperty.flat_of_tensorIso (β_ D F ≪≫ eFD)
  let er : ((derivedTensor (ModuleCat.{u + 1} A) X).obj SF).obj SD ≅
      constantComplex A X :=
    singleFunctorObjTensorIso F D hflat ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso eFD ≪≫
      singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X
  let el : ((derivedTensor (ModuleCat.{u + 1} A) X).obj SD).obj SF ≅
      constantComplex A X :=
    singleFunctorObjTensorIso D F hflatD ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso (β_ D F ≪≫ eFD) ≪≫
      singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X
  refine ⟨SD⟦-n⟧, ⟨D, hD, hsD, ⟨Iso.refl _⟩⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso eM).app _ ≪≫
      derivedTensorShiftIso _ SF SD n (-n) ≪≫ (shiftFunctor _ _).mapIso er ≪≫
      (shiftFunctorZero' _ (n + -n) (add_neg_cancel n)).app _
  · exact ((derivedTensor (ModuleCat.{u + 1} A) X).obj _).mapIso eM ≪≫
      derivedTensorShiftIso _ SD SF (-n) n ≪≫ (shiftFunctor _ _).mapIso el ≪≫
      (shiftFunctorZero' _ (-n + n) (neg_add_cancel n)).app _

/-- Lines of fixed shape descend through an arbitrary small jointly surjective etale
family, with the global line sheaf equal to `H^(-n)(M)`. Derived morphisms are invertible
if their inverse images through that family are invertible.

Source: blueprint main-20261015, `thm-asd-smooth-tensor.proof.md`, paragraph 4;
Stacks Tags 03Q1, 093Q, 08J5 and 05RT
(blueprint: lem-sf-shifted-etale-lines-locality).

Proof:
1. Exact constant-coefficient inverse image commutes with cohomology on all unbounded
complexes, by the exact-functor derived construction. If each pullback is `L_i[n]`, all
cohomology outside degree `-n` vanishes after pullback. Joint-surjectivity conservativity
for sheaves therefore makes each of these cohomology sheaves zero globally.
2. The single-degree truncation criterion gives `M ≅ H^(-n)(M)[n]`; apply cohomology to
the single-object presentation to identify its sheaf with this particular cohomology.
This constructs a global sheaf and does not glue presentations in the derived category.
3. Exact pullback identifies the inverse image of this cohomology sheaf with `L_i`.
Etale inverse image is restriction to the localized site. Trivialize each `L_i` and
compose the covers. A constant value module on a nonempty member is `A`, by the
constant-stalk comparison and inverse-image-stalk comparison. The resulting cover
therefore trivializes the global cohomology sheaf with value `A`. It is locally constant;
lifting geometric points to this cover and the field-extension stalk comparison give
all its separably closed stalks isomorphic to `A`.
4. For a morphism, exact pullback identifies the pulled-back cohomology maps with the
cohomology maps of its pullback. They are isomorphisms. Sheaf conservativity makes each
global cohomology map invertible, and the unbounded derived cohomology criterion makes
the morphism invertible. An arbitrary small cover can be reduced to a family indexed by
points of `X` by selecting one covering member over each point; no finite subcover or
nonemptiness is needed.
5. On the empty scheme the empty covering forces all sheaf sections to be zero. All
complexes, the constant unit and cohomology sheaves are zero up to isomorphism, and all
morphisms are invertible. An empty jointly surjective family forces this case. For the
zero coefficient ring all unital modules are zero, so the same conclusions hold. -/
theorem shiftedEtaleLines_descent
    {ι : Type w} {U : ι → Scheme.{u}} (v : ∀ i : ι, U i ⟶ X)
    [∀ i : ι, AlgebraicGeometry.Etale (v i)]
    (hv : ∀ x : X, ∃ (i : ι) (y : U i), (v i).base y = x) :
    (∀ (M : DerivedCategoryModule A X) (n : ℤ),
      (∀ i : ι, IsShiftedRankOneLocalSystem
        ((L((v i)^*[ModuleCat.{u + 1} A])).obj M) n) →
      IsLocallyConstantSheaf ((_root_.DerivedCategory.homologyFunctor _ (-n)).obj M) ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        Nonempty ((pointSmallEtale s).sheafFiber.obj
          ((_root_.DerivedCategory.homologyFunctor _ (-n)).obj M) ≅ ModuleCat.of A A)) ∧
      Nonempty (M ≅ ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((_root_.DerivedCategory.homologyFunctor _ (-n)).obj M))⟦n⟧)) ∧
    (∀ (K K' : DerivedCategoryModule A X) (α : K ⟶ K'),
      (∀ i : ι, IsIso ((L((v i)^*[ModuleCat.{u + 1} A])).map α)) → IsIso α) := by
  classical
  choose j y hy using hv
  let v' (x : X) : U (j x) ⟶ X := v (j x)
  have hv' : ∀ x : X, ∃ (z : X) (t : U (j z)), (v' z).base t = x :=
    fun x ↦ ⟨x, y x, hy x⟩
  constructor
  · intro M n hM
    obtain ⟨F, hF, hs, ⟨e⟩⟩ :=
      IsShiftedRankOneLocalSystem.of_jointlySurjective v' hv' (fun x ↦ hM (j x))
    let e' : M ≅ (_root_.DerivedCategory.singleFunctor _ (-n)).obj F :=
      e ≪≫ ((_root_.DerivedCategory.singleFunctors _).shiftIso n (-n) 0
        (add_neg_cancel n)).app F
    let eH : ((_root_.DerivedCategory.homologyFunctor _ (-n)).obj M) ≅ F :=
      (_root_.DerivedCategory.homologyFunctor _ (-n)).mapIso e' ≪≫
        (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-n)).app F
    refine ⟨IsLocallyConstantSheaf.of_iso eH.symm, ?_, ⟨?_⟩⟩
    · intro Ω _ _ t
      exact ⟨(pointSmallEtale t).sheafFiber.mapIso eH ≪≫ (hs Ω t).some⟩
    · exact e ≪≫ (shiftFunctor _ n).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso eH.symm)
  · intro K K' α hα
    exact isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective A v' hv' α
      (fun x ↦ hα (j x))

end AlgebraicGeometry.Etale
