/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.AlgebraicGeometry.AbelianDerivedGlobalExtPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-! # Detecting cohomology pullback with exact conservative global sections

Source: Stacks Project, Tags 01F8 and 03Q9, derived-unit description of pullback.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The degree-q map of sheaves induced by the derived inverse-image/direct-image unit. -/
noncomputable def derivedPullbackUnitHomology {Y E : Scheme.{u}} (p : Y ⟶ E)
    (G : Sheaf E.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :=
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).derivedPlus.unit.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G))

/-- With exact conservative sections, cohomology pullback is invertible precisely when
its derived unit is invertible on the specified homology sheaf.
Source: Stacks Project, Tags 01F8 and 03Q9, exact-sections Leray argument.
(blueprint: lem-weil-pbc-cohomology-pullback-exact-conservative).
Proof: the Ext/derived-global-sections comparison identifies pullback with homology of
RΓ applied to the derived unit followed by Leray. Leray is an isomorphism. Exactness
identifies RΓ with termwise Γ, which commutes with homology. Conservativity of Γ then
reflects invertibility of the homology of the unit. -/
theorem bijective_cohomologyMap_iff_isIso_derivedPullbackUnitHomology
    {Y E : Scheme.{u}} (p : Y ⟶ E)
    [PreservesFiniteColimits (Sheaf.Γ E.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(Sheaf.Γ E.smallEtaleTopology AddCommGrpCat.{u + 1}).ReflectsIsomorphisms]
    (G : Sheaf E.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (cohomologyMap p G q) ↔
      IsIso (derivedPullbackUnitHomology p G q) := by
  let Γ := Sheaf.Γ E.smallEtaleTopology AddCommGrpCat.{u + 1}
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let η := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).derivedPlus.unit.app K
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)
  obtain ⟨b₁, b₂, hb⟩ := exists_addEquiv_derivedGlobal_ext_pullback p G q
  have hbij : Function.Bijective (cohomologyMap p G q) ↔
      Function.Bijective (H.map
        (Γ.rightDerivedFunctorPlus.map η ≫
          (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (lowerStar AddCommGrpCat.{u + 1} p) Γ _ _ _ _
            (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
              (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p))
            (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} p)).hom.app
              ((upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategoryPlus.obj K))) := by
    have heq : cohomologyMap p G q ∘ b₁ = b₂ ∘ _ := funext fun x ↦ (hb x).symm
    constructor
    · intro h
      have hc := h.comp b₁.bijective
      rw [heq] at hc
      exact (Function.Bijective.of_comp_iff' b₂.bijective _).mp hc
    · intro h
      have hc := b₂.bijective.comp h
      rw [← heq] at hc
      exact (Function.Bijective.of_comp_iff _ b₁.bijective).mp hc
  rw [hbij, ← ConcreteCategory.isIso_iff_bijective, Functor.map_comp]
  rw [isIso_comp_right_iff]
  let e := Functor.isoWhiskerRight Γ.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus H ≪≫
    (Γ.mapDerivedCategoryPlusHomologyFunctorIso (q : ℤ)).symm
  change IsIso ((Γ.rightDerivedFunctorPlus ⋙ H).map η) ↔ _
  rw [NatIso.isIso_map_iff e η]
  exact isIso_iff_of_reflects_iso (derivedPullbackUnitHomology p G q) Γ

end AlgebraicGeometry.Etale
