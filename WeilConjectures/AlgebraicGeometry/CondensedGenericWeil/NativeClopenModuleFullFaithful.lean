/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.CondensedGenericWeilData
public import Mathlib.CategoryTheory.Pi.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.DisjointUnion

/-! # Full faithfulness of native clopen component restriction

Source: Weil II (1.1.12), maps on the disjoint component cover.
(blueprint: lem-dl-a1-native-clopen-module-full-faithful).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u vC vD uC uD uI
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

attribute [local irreducible] CondensedRing.upperStar

private def jointlyFullyFaithful
    {C : Type uC} [Category.{vC} C] {I : Type uI}
    {D : I → Type uD} [∀ i, Category.{vD} (D i)]
    (L : ∀ i, C ⥤ D i) (R : ∀ i, D i ⥤ C) (a : ∀ i, L i ⊣ R i)
    (h : ∀ N, IsLimit (Fan.mk N fun i ↦ (a i).unit.app N)) :
    (Functor.pi' L).FullyFaithful where
  preimage {M N} f := Fan.IsLimit.lift (h N)
    (fun i ↦ (a i).homEquiv M ((L i).obj N) (f i))
  map_preimage {M N} f := by
    funext i
    apply ((a i).homEquiv M ((L i).obj N)).injective
    rw [Adjunction.homEquiv_unit]
    change (a i).unit.app M ≫ (L i ⋙ R i).map _ = _
    rw [← (a i).unit.naturality]
    exact Fan.IsLimit.fac (h N) _ i
  preimage_map {M N} f := by
    apply Fan.IsLimit.hom_ext (h N)
    intro i
    rw [Fan.IsLimit.fac]
    change (a i).unit.app M ≫ (L i ⋙ R i).map f =
      (𝟭 C).map f ≫ (a i).unit.app N
    exact ((a i).unit.naturality f).symm

/-- Restriction to every member of a family, using the actual coefficient pullback functors.
Source: the disjoint component cover in Weil II (1.1.12).
(blueprint: lem-dl-a1-native-clopen-module-full-faithful). -/
def nativeClopenRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {I : Type u} {X : Scheme.{u}} {Y : I → Scheme.{u}}
    (j : ∀ i, Y i ⟶ X) :
    RealCondensedFibre.Modules Λ X ⥤ ∀ i, RealCondensedFibre.Modules Λ (Y i) :=
  Functor.pi' (fun i ↦ CondensedRing.upperStar Λ (j i))

/-- Native module maps glue uniquely across a finite disjoint component cover.
Source: Weil II (1.1.12), sheaf gluing on the disjoint open cover.
(blueprint: lem-dl-a1-native-clopen-module-full-faithful).

Proof: the published native unit fan expresses each target module as the product
of the pushforwards of its restrictions. Given component maps, apply each
pullback--pushforward adjunction and lift the resulting family into this fan.
The fan projection equations and naturality of the adjunction units show that
restriction gives the original maps. The same equations show that lifting the
restrictions of a global map returns that map. These are inverse maps on Hom
sets, without changing the coefficient model or any module carrier. -/
theorem native_clopen_restriction_full_faithful
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {I : Type u} [Finite I] {X : Scheme.{u}} {Y : I → Scheme.{u}}
    (j : ∀ i, Y i ⟶ X) (hc : IsColimit (Cofan.mk X j)) :
    (nativeClopenRestriction Λ j).Full ∧ (nativeClopenRestriction Λ j).Faithful := by
  let h := jointlyFullyFaithful
    (fun i ↦ CondensedRing.upperStar Λ (j i))
    (fun i ↦ CondensedRing.lowerStar Λ (j i))
    (fun i ↦ CondensedRing.upperStarLowerStarAdjunction Λ (j i))
    (CondensedRing.isLimitFanUnitOfIsColimitCofan Λ hc)
  exact ⟨h.full, h.faithful⟩

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
