/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralAcyclic

/-!
# `F_X` is a finite free `E_X`-module

Let `ℓ` be a prime and `E ≤ F` finite subextensions of `ℚ̄_ℓ / ℚ_ℓ`. For a basis `b₁, …, bₙ` of
`F` over `E`, the map `E̲ⁿ ⟶ F̲`, `(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism of condensed abelian groups
(`Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`): its inverse is given
by the coordinates, which are continuous since `F` is a finite-dimensional `ℚ_ℓ`-vector space.
Here the multiplication by `bᵢ` is the action of the constant global section `bᵢ` of `F̲` on the
regular module (`Profinite.globalSmul_continuousMapConstRingHom`). Pulling back along `p_X`, the
same holds for `E_X ⟶ F_X` on any scheme `X`
(`AlgebraicGeometry.ProEtale.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

/-- The action of a global section on the regular module is invariant under isomorphisms of
monoid objects. -/
lemma globalSmul_comp_hom_regular {C : Type*} [Category* C] [MonoidalCategory C] {A B : C}
    [MonObj A] [MonObj B] (e : A ≅ B) [IsMonHom e.hom] (σ : 𝟙_ C ⟶ A) :
    globalSmul (σ ≫ e.hom) (regular B) = e.inv ≫ globalSmul σ (regular A) ≫ e.hom := by
  change (λ_ B).inv ≫ (σ ≫ e.hom) ▷ B ≫ μ[B] = e.inv ≫ ((λ_ A).inv ≫ σ ▷ A ≫ μ[A]) ≫ e.hom
  rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def,
    Category.assoc, leftUnitor_inv_naturality_assoc, ← comp_whiskerRight_assoc,
    whisker_exchange_assoc, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The action of the image `ε ≫ F σ` of a global section on the regular module `F A` is the
image of the action of `σ` on the regular module `A`, for a lax monoidal functor `F`. -/
lemma globalSmul_regular_obj {C D : Type*} [Category* C] [MonoidalCategory C] [Category* D]
    [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] {A : C} [MonObj A] (σ : 𝟙_ C ⟶ A) :
    globalSmul (Functor.LaxMonoidal.ε F ≫ F.map σ) (regular (F.obj A)) =
      F.map (globalSmul σ (regular A)) := by
  rw [globalSmul, globalSmul, Functor.map_comp, Functor.map_comp,
    ← Functor.LaxMonoidal.left_unitality_inv, Category.assoc, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, comp_whiskerRight_assoc]
  rfl

end CategoryTheory.Mod

namespace Profinite

section GlobalSmul

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- On the presheaf `C(-, T)`, the constant global section `t` acts on the regular module by
multiplication by `t`. -/
lemma globalSmul_continuousMapConstSection_presheaf (t : T) :
    Mod.globalSmul ((continuousMapRingPresheaf.{u} T).ringHomΓCompForget₂
      (continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl) t).hom
      (Mod.regular (continuousMapRingPresheaf.{u} T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})) =
    (continuousMapRingObjMulLeft.{u} T t).hom := by
  apply (cancel_epi (λ_ _).hom).1
  simp only [Mod.globalSmul, Iso.hom_inv_id_assoc]
  ext S : 2
  refine AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun n a ↦ ?_)
  change ((n.down : ULift.{u + 1} C(S.unop, T)) * ULift.up (ContinuousMap.const _ t)) *
      (show ULift.{u + 1} C(S.unop, T) from a) =
    ULift.up (ContinuousMap.const _ t * (n.down • (show ULift.{u + 1} C(S.unop, T) from a)).down)
  apply ULift.ext
  ext s
  change ((n.down : C(S.unop, T)) * ContinuousMap.const _ t *
    (show ULift.{u + 1} C(S.unop, T) from a).down : C(S.unop, T)) s =
      t * (n.down • (show ULift.{u + 1} C(S.unop, T) from a).down) s
  simp [zsmul_eq_mul]
  ring


/-- **The constant global section `t` of `T̲ = C(-, T)` acts on the regular module by
multiplication by `t`.** -/
lemma globalSmul_continuousMapConstRingHom (t : T) :
    Mod.globalSmul (continuousMapConstRingHom.{u} T t).hom
      (Mod.regular (continuousMapRingObj.{u} T)) = continuousMapRingObjMulLeft T t := by
  let J := coherentTopology Profinite.{u}
  let e := Sheaf.sheafifyRingPresheafIso.{u + 1, u, u + 1} J (continuousMapRingSheaf.{u} T)
  let sP := (continuousMapRingPresheaf.{u} T).ringHomΓCompForget₂
      (continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl) t
  have hσ : (continuousMapConstRingHom.{u} T t).hom =
      (Functor.LaxMonoidal.ε (presheafToSheaf J Ab.{u + 1}) ≫
        (presheafToSheaf J Ab.{u + 1}).map sP.hom) ≫ e.hom := rfl
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafifyRingPresheafIso_hom.{u + 1, u, u + 1} J _
  rw [hσ]
  erw [Mod.globalSmul_comp_hom_regular e]
  have h₁ : Mod.globalSmul (Functor.LaxMonoidal.ε (presheafToSheaf J Ab.{u + 1}) ≫
        (presheafToSheaf J Ab.{u + 1}).map sP.hom)
      (Mod.regular ((presheafToSheaf J Ab.{u + 1}).obj
        (continuousMapRingPresheaf.{u} T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}))) =
      (presheafToSheaf J Ab.{u + 1}).map (Mod.globalSmul sP.hom
        (Mod.regular (continuousMapRingPresheaf.{u} T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}))) := by
    rw [Mod.globalSmul, Mod.globalSmul, Functor.map_comp, Functor.map_comp,
      ← Functor.LaxMonoidal.left_unitality_inv, Category.assoc, Category.assoc,
      ← Functor.LaxMonoidal.μ_natural_left_assoc, comp_whiskerRight_assoc]
    rfl
  rw [globalSmul_continuousMapConstSection_presheaf] at h₁
  refine (congrArg (fun g ↦ e.inv ≫ g ≫ e.hom) h₁).trans ?_
  have h₂ := (sheafificationAdjunction J Ab.{u + 1}).counit.naturality
    (continuousMapRingObjMulLeft.{u} T t)
  exact (Iso.inv_comp_eq e).2 h₂


end GlobalSmul

section Coordinates

variable {T T' : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [TopologicalSpace T']
  [CommRing T'] [IsTopologicalRing T']

/-- Postcomposition with a continuous additive map `g : T →+ T'`, as a morphism of condensed
abelian groups `C(-, T) ⟶ C(-, T')`. -/
noncomputable def continuousMapRingObjAddMap (g : T →+ T') (hg : Continuous g) :
    continuousMapRingObj.{u} T ⟶ continuousMapRingObj T' :=
  ⟨{ app _ := AddCommGrpCat.ofHom
        { toFun a := ULift.up ⟨fun s ↦ g (a.down s), hg.comp a.down.continuous⟩
          map_zero' := ULift.ext _ _ (ContinuousMap.ext fun _ ↦ map_zero g)
          map_add' a b :=
            ULift.ext _ _ (ContinuousMap.ext fun s ↦ map_add g (a.down s) (b.down s)) }
     naturality _ _ _ := rfl }⟩

open _root_.PadicAlgCl

attribute [local instance] Abelian.hasFiniteBiproducts

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ} (hF : E ≤ F)

lemma exists_isIso_biproductDesc_padicSubfieldRingObjMap_mulLeft :
    ∃ (n : ℕ) (b : Fin n → F), IsIso (biproduct.desc fun i ↦
      padicSubfieldRingObjMap ℓ hF ≫ continuousMapRingObjMulLeft F (b i) :
        ⨁ (fun _ : Fin n ↦ continuousMapRingObj.{u} E) ⟶ continuousMapRingObj F) := by
  let : Algebra E F := (IntermediateField.inclusion hF).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[ℓ] E F := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : FiniteDimensional E F := FiniteDimensional.right ℚ_[ℓ] E F
  let b := Module.finBasis E F
  let c (i : Fin (Module.finrank E F)) : continuousMapRingObj.{u} F ⟶ continuousMapRingObj E :=
    continuousMapRingObjAddMap (b.coord i).toAddMonoidHom
      ((b.coord i).restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional
  refine ⟨_, fun i ↦ b i, ⟨biproduct.lift c, ?_, ?_⟩⟩
  · refine biproduct.hom_ext' _ _ fun j ↦ biproduct.hom_ext _ _ fun k ↦ ?_
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id,
      biproduct.ι_π]
    split_ifs with h
    · subst h
      rw [eqToHom_refl]
      ext S a
      apply ULift.ext
      refine ContinuousMap.ext fun s ↦ ?_
      change b.coord j (b j * algebraMap E F (a.down s)) = a.down s
      rw [mul_comm, ← Algebra.smul_def]
      simp
    · ext S a
      apply ULift.ext
      refine ContinuousMap.ext fun s ↦ ?_
      change b.coord k (b j * algebraMap E F (a.down s)) = 0
      rw [mul_comm, ← Algebra.smul_def]
      simp [h]
  · rw [biproduct.lift_desc]
    ext S a
    have h₁ := (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
      (evaluation _ _).obj S).map_sum (fun j ↦ c j ≫ padicSubfieldRingObjMap ℓ hF ≫
        continuousMapRingObjMulLeft F (b j)) Finset.univ
    refine ULift.ext _ _ (ContinuousMap.ext fun s ↦ ?_)
    let ev : (continuousMapRingObj.{u} F).obj.obj S →+ F :=
      { toFun y := (show ULift.{u + 1} C(S.unop, F) from y).down s
        map_zero' := rfl
        map_add' _ _ := rfl }
    have h₂ := congrArg (fun φ ↦ ev (AddCommGrpCat.homAddEquiv φ a)) h₁
    simp only [map_sum, AddMonoidHom.finsetSum_apply] at h₂
    refine h₂.trans ?_
    change ∑ j, b j * algebraMap E F (b.coord j (a.down s)) = a.down s
    simp only [mul_comm (b _), ← Algebra.smul_def, Module.Basis.coord_apply]
    exact b.sum_repr _

/-- **`F̲` is a finite free `E̲`-module**: for a basis `b` of `F` over `E`, the map `E̲ⁿ ⟶ F̲`,
`(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism. -/
lemma exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul :
    ∃ (n : ℕ) (b : Fin n → F), IsIso (biproduct.desc fun i ↦
      padicSubfieldRingObjMap ℓ hF ≫ Mod.globalSmul (continuousMapConstRingHom F (b i)).hom
        (Mod.regular (continuousMapRingObj F)) :
        ⨁ (fun _ : Fin n ↦ continuousMapRingObj.{u} E) ⟶ continuousMapRingObj F) := by
  obtain ⟨n, b, h⟩ := exists_isIso_biproductDesc_padicSubfieldRingObjMap_mulLeft ℓ hF
  refine ⟨n, b, ?_⟩
  simpa only [globalSmul_continuousMapConstRingHom] using h

end Coordinates

end Profinite

namespace AlgebraicGeometry.ProEtale

open Functor.LaxMonoidal

attribute [local instance] Abelian.hasFiniteBiproducts

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {E F : PadicAlgCl.FiniteIntermediateField ℓ}
  (hF : E ≤ F)

/-- **`F_X` is a finite free `E_X`-module**: if `b₁, …, bₙ` is a basis of `F` over `E`, in the
sense that `E̲ⁿ ⟶ F̲`, `(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism, then so is its pullback
`E_Xⁿ ⟶ F_X`, `bᵢ` acting through the constant global section `p_X^* bᵢ`. -/
lemma isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul {n : ℕ} (b : Fin n → F)
    (h : IsIso (biproduct.desc fun i ↦
      Profinite.padicSubfieldRingObjMap ℓ hF ≫ Mod.globalSmul
        (Profinite.continuousMapConstRingHom F (b i)).hom
          (Mod.regular (Profinite.continuousMapRingObj F)) :
        ⨁ (fun _ : Fin n ↦ Profinite.continuousMapRingObj.{u} E) ⟶
          Profinite.continuousMapRingObj F)) :
    IsIso (biproduct.desc fun i ↦
      padicSubfieldRingObjMap X ℓ hF ≫ Mod.globalSmul (ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom F (b i)).hom)
        (Mod.regular (padicSubfieldRingObj X ℓ F)) :
        ⨁ (fun _ : Fin n ↦ padicSubfieldRingObj X ℓ E) ⟶ padicSubfieldRingObj X ℓ F) := by
  have e : (fun i ↦ padicSubfieldRingObjMap X ℓ hF ≫ Mod.globalSmul (ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom F (b i)).hom)
        (Mod.regular (padicSubfieldRingObj X ℓ F))) = fun i ↦ (upperStarFromPoint X).map
          (Profinite.padicSubfieldRingObjMap ℓ hF ≫ Mod.globalSmul
            (Profinite.continuousMapConstRingHom F (b i)).hom
              (Mod.regular (Profinite.continuousMapRingObj F))) := by
    funext i
    rw [Functor.map_comp, Mod.globalSmul_regular_obj]
  rw [e, ← biproduct.mapBiproduct_inv_map_desc]
  exact IsIso.comp_isIso' inferInstance
    (@Functor.map_isIso _ _ _ _ _ _ (upperStarFromPoint X) _ h)

end AlgebraicGeometry.ProEtale
