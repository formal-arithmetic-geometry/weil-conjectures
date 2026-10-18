/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.IhomComp

/-!
# Transport of internal homs of modules along a lax monoidal functor

Let `G : C ⥤ D` be a lax braided functor and `ρ : B ⟶ G A` a morphism of commutative monoids,
`F = mapModComap ρ` the induced functor on modules. Suppose given comparison morphisms
`c M N : F Hom_A(M, N) ⟶ Hom_B(F M, F N)` whose uncurried forms are `G` of the evaluations. Given
isomorphisms `φ_M : F M ≅ M'`, `φ_N : F N ≅ N'`, we get `F Hom_A(M, N) ⟶ Hom_B(M', N')`
(`CategoryTheory.Mod.trHom`), and morphisms into internal homs whose uncurried forms are
compatible with the `φ`'s are compatible with these (`CategoryTheory.Mod.map_comp_trHom`). As an
application, `CategoryTheory.Mod.ihomIhomComparison` is compatible with such transports
(`CategoryTheory.Mod.map_ihomIhomComparison_comp_trHom`); this is used both for the pullback
along a weakly étale morphism and for the Weil structures.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory MonObj Limits Functor.LaxMonoidal

namespace CategoryTheory.Mod

open scoped Obj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {B : D} [MonObj B]
  [SymmetricCategory D] [IsCommMonObj B] [Abelian D] [MonoidalPreadditive D]
  [IsGrothendieckAbelian.{v'} D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorRight X)]
  {G : C ⥤ D} [G.LaxMonoidal] (ρ : B ⟶ G.obj A) [IsMonHom ρ]
  (c : ∀ M N : Mod C A, (mapModComap ρ).obj ((ihom M).obj N) ⟶
    (ihom ((mapModComap ρ).obj M)).obj ((mapModComap ρ).obj N))

/-- The transport `F Hom_A(M, N) ⟶ Hom_B(F M, F N) ⟶ Hom_B(M', N')` along `φ_M : F M ≅ M'` and
`φ_N : F N ≅ N'`. -/
noncomputable def trHom {M N : Mod C A} {M' N' : Mod D B} (φM : (mapModComap ρ).obj M ≅ M')
    (φN : (mapModComap ρ).obj N ≅ N') :
    (mapModComap ρ).obj ((ihom M).obj N) ⟶ (ihom M').obj N' :=
  c M N ≫ (ihomMap φM.inv).app _ ≫ (ihom M').map φN.hom

/-- The transport `F Hom_A(M, N) ≅ Hom_B(M', N')`, when the comparison is an isomorphism. -/
noncomputable def trIso [∀ M N, IsIso (c M N)] {M N : Mod C A} {M' N' : Mod D B}
    (φM : (mapModComap ρ).obj M ≅ M') (φN : (mapModComap ρ).obj N ≅ N') :
    (mapModComap ρ).obj ((ihom M).obj N) ≅ (ihom M').obj N' :=
  asIso (c M N) ≪≫ (ihomMapIso φM.symm).app _ ≪≫ (ihom M').mapIso φN

lemma trIso_hom [∀ M N, IsIso (c M N)] {M N : Mod C A} {M' N' : Mod D B}
    (φM : (mapModComap ρ).obj M ≅ M') (φN : (mapModComap ρ).obj N ≅ N') :
    (trIso ρ c φM φN).hom = trHom ρ c φM φN :=
  rfl

variable {ρ c}
variable (hc : ∀ M N : Mod C A, uncurryHom (c M N) = Functor.LaxMonoidal.μ G _ _ ≫ G.map (evaluation M N))

include hc in
/-- The evaluation is compatible with the transport. -/
lemma trHom_evaluation {M N : Mod C A} {M' N' : Mod D B} (φM : (mapModComap ρ).obj M ≅ M')
    (φN : (mapModComap ρ).obj N ≅ N') :
    ((trHom ρ c φM φN).hom ⊗ₘ φM.hom.hom) ≫ evaluation M' N' =
      Functor.LaxMonoidal.μ G _ _ ≫ G.map (evaluation M N) ≫ φN.hom.hom := by
  have hφ : φM.hom.hom ≫ φM.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [trHom, Mod.comp_hom', Mod.comp_hom', tensorHom_def', comp_whiskerRight,
    comp_whiskerRight]
  simp only [Category.assoc]
  rw [evaluation_naturality, evaluation_ihomMap_assoc, ← whisker_exchange_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, hφ, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, ← Category.assoc, ← uncurryHom, hc, Category.assoc]

include hc in
/-- A morphism into an internal hom whose uncurried form is compatible with the `φ`'s is
compatible with the transport. -/
lemma map_comp_trHom {P M N : Mod C A} {P' M' N' : Mod D B} (φP : (mapModComap ρ).obj P ≅ P')
    (φM : (mapModComap ρ).obj M ≅ M') (φN : (mapModComap ρ).obj N ≅ N')
    (κ : P ⟶ (ihom M).obj N) (κ' : P' ⟶ (ihom M').obj N')
    (h : (φP.hom.hom ⊗ₘ φM.hom.hom) ≫ uncurryHom κ' =
      Functor.LaxMonoidal.μ G _ _ ≫ G.map (uncurryHom κ) ≫ φN.hom.hom) :
    (mapModComap ρ).map κ ≫ trHom ρ c φM φN = φP.hom ≫ κ' := by
  have : IsIso φM.hom.hom := inferInstanceAs (IsIso ((Mod.forget _).map φM.hom))
  apply uncurryHom_injective
  rw [← cancel_epi (((mapModComap ρ).obj P).X ◁ φM.hom.hom)]
  simp only [uncurryHom, Mod.comp_hom', comp_whiskerRight, Category.assoc] at h ⊢
  rw [whisker_exchange_assoc]
  conv_lhs => rw [← tensorHom_def'_assoc, trHom_evaluation hc]
  conv_rhs => rw [← tensorHom_def'_assoc, h]
  rw [G.map_comp]
  exact (μ_natural_left_assoc G κ.hom M.X _).trans (by simp only [Category.assoc])

include hc in
/-- A morphism into an internal hom out of a tensor product, whose uncurried form is compatible
with the `φ`'s, is compatible with the transport. -/
lemma tensorHom_comp_eq_of_uncurry {P M N Q : Mod C A} {P' M' N' Q' : Mod D B}
    (φP : (mapModComap ρ).obj P ≅ P') (φM : (mapModComap ρ).obj M ≅ M')
    (φN : (mapModComap ρ).obj N ≅ N') (φQ : (mapModComap ρ).obj Q ≅ Q')
    (u : P.X ⊗ M.X ⟶ ((ihom N).obj Q).X) (u' : P'.X ⊗ M'.X ⟶ ((ihom N').obj Q').X)
    (h : ((φP.hom.hom ⊗ₘ φM.hom.hom) ⊗ₘ φN.hom.hom) ≫ u' ▷ N'.X ≫ evaluation N' Q' =
      Functor.LaxMonoidal.μ G _ _ ▷ G.obj N.X ≫ Functor.LaxMonoidal.μ G _ _ ≫
        G.map (u ▷ N.X ≫ evaluation N Q) ≫ φQ.hom.hom) :
    (φP.hom.hom ⊗ₘ φM.hom.hom) ≫ u' =
      Functor.LaxMonoidal.μ G _ _ ≫ G.map u ≫ (trHom ρ c φN φQ).hom := by
  have : IsIso φN.hom.hom := inferInstanceAs (IsIso ((Mod.forget _).map φN.hom))
  apply hom_ext_of_evaluation (D := N')
  rw [← cancel_epi ((((mapModComap ρ).obj P).X ⊗ ((mapModComap ρ).obj M).X) ◁ φN.hom.hom)]
  rw [comp_whiskerRight_assoc, ← tensorHom_def'_assoc]
  erw [h]
  symm
  rw [comp_whiskerRight_assoc, comp_whiskerRight_assoc]
  erw [whisker_exchange_assoc, whisker_exchange_assoc, ← tensorHom_def'_assoc, trHom_evaluation hc,
    μ_natural_left_assoc]
  rw [G.map_comp, Category.assoc]
  rfl

end CategoryTheory.Mod
