/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTateWeilLaw
public import WeilConjectures.CategoryTheory.Monoidal.MapIsoUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeFirst

/-!
# The Weil structure of the trivialized Tate twists `ℚ̄_ℓ(d)`, `d ≥ 0`

The canonical Weil structure `Fr^* p^* M ≅ p^* M` of pulled-back module objects
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberProjUpperStarFrobeniusIso`) is a
monoidal natural isomorphism. Hence the trivializations `p^* ℚ̄_ℓ(d) ≅ 𝟙` of the tensor powers
`ℚ̄_ℓ(d) = ℚ̄_ℓ(1)^{⊗ d}` (`AlgebraicGeometry.ProEtale.CondensedRing.purity_tateTwistNatTrivialization`),
built from the trivialization of `p^* ℚ̄_ℓ(1)` by the strong monoidality of `p^*`, satisfy the
Weil law with the scalar `q^d`: `q^d` times the canonical Weil structure followed by the
trivialization is `Fr^*` of the trivialization followed by the unit structure
(`AlgebraicGeometry.ProEtale.CondensedRing.purity_tateTwistNatTrivialization_weil`).
-/

@[expose] public section

universe u v u' v'

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {D : Type u'} [Category.{v'} D]
  [MonoidalCategory D]

/-- The oplax left unitality on the unit: `δ_{𝟙,𝟙}` followed by `η ⊗ η` and the left unitor is
`F (λ_𝟙)` followed by `η`. -/
lemma Functor.OplaxMonoidal.purity_δ_unit_comp_tensorHom_η_comp_leftUnitor_hom (F : C ⥤ D)
    [F.OplaxMonoidal] :
    δ F (𝟙_ C) (𝟙_ C) ≫ (η F ⊗ₘ η F) ≫ (λ_ (𝟙_ D)).hom = F.map (λ_ (𝟙_ C)).hom ≫ η F := by
  have h := Functor.OplaxMonoidal.oplax_left_unitality F (𝟙_ C)
  rw [tensorHom_def, Category.assoc, leftUnitor_naturality, ← cancel_epi (F.map (λ_ (𝟙_ C)).inv),
    ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp,
    ← reassoc_of% h, Iso.inv_hom_id_assoc]

/-- Integer scalars of a tensor product of morphisms in a preadditive monoidal category. -/
lemma purity_zsmul_tensorHom_zsmul [Preadditive D] [MonoidalPreadditive D] {X₁ Y₁ X₂ Y₂ : D}
    (N N' : ℤ) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (N • f) ⊗ₘ (N' • g) = (N * N') • (f ⊗ₘ g) := by
  have h1 : (N • f) ▷ X₂ = N • (f ▷ X₂) := (tensorRight X₂).map_zsmul
  have h2 : Y₁ ◁ (N' • g) = N' • (Y₁ ◁ g) := (tensorLeft Y₁).map_zsmul
  rw [tensorHom_def, tensorHom_def, h1, h2, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    mul_comm, mul_zsmul]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Monoidality of the Weil structure of pulled-back module objects -/

section Monoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The composition isomorphisms of pullbacks of module objects are monoidal (the public form of
the private `upper_comp_monoidal`). -/
instance purity_isMonoidal_upperStarComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp Λ f g).hom :=
  upper_comp_monoidal Λ f g

/-- The transport of pullbacks along an equation of morphisms is monoidal. -/
instance purity_isMonoidal_upperStarCongr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    NatTrans.IsMonoidal (upperStarCongr Λ h).hom := by
  subst h
  rw [upperStarCongr_self, Iso.refl_hom]
  infer_instance

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- **The Weil structure of pulled-back module objects is monoidal.** -/
instance purity_isMonoidal_geometricFiberProjUpperStarFrobeniusIso_hom :
    NatTrans.IsMonoidal (geometricFiberProjUpperStarFrobeniusIso Λ f).hom := by
  dsimp only [geometricFiberProjUpperStarFrobeniusIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

/-- The Weil structure of `p^* 𝟙` followed by the unit comparison `p^* 𝟙 ⟶ 𝟙` is `Fr^*` of the
unit comparison followed by the unit comparison of `Fr^*`. -/
lemma purity_geometricFiberProjUpperStarFrobeniusIso_hom_app_unit_comp_η :
    (geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app (𝟙_ _) ≫
        η (upperStar Λ f.geometricFiberProj) =
      (upperStar Λ f.geometricGaloisFrobenius.hom).map (η (upperStar Λ f.geometricFiberProj)) ≫
        η (upperStar Λ f.geometricGaloisFrobenius.hom) := by
  have h := NatTrans.IsMonoidal.unit (τ := (geometricFiberProjUpperStarFrobeniusIso Λ f).hom)
  rw [Functor.LaxMonoidal.comp_ε, Category.assoc] at h
  rw [← cancel_epi (ε (upperStar Λ f.geometricGaloisFrobenius.hom) ≫
    (upperStar Λ f.geometricGaloisFrobenius.hom).map (ε (upperStar Λ f.geometricFiberProj)))]
  simp only [Category.assoc]
  rw [reassoc_of% h, Functor.Monoidal.ε_η, ← Functor.map_comp_assoc, Functor.Monoidal.ε_η,
    Functor.map_id, Category.id_comp, Functor.Monoidal.ε_η]

/-- The Weil structure of `p^* (M ⊗ N)` through the tensor comparisons. -/
lemma purity_geometricFiberProjUpperStarFrobeniusIso_hom_app_tensorObj
    (M N : Mod (Sheaf (ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀)) :
    (geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app (M ⊗ N) =
      (upperStar Λ f.geometricGaloisFrobenius.hom).map (δ (upperStar Λ f.geometricFiberProj) M N) ≫
        δ (upperStar Λ f.geometricGaloisFrobenius.hom) _ _ ≫
        ((geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app M ⊗ₘ
          (geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app N) ≫
        μ (upperStar Λ f.geometricFiberProj) M N := by
  have h := NatTrans.IsMonoidal.tensor (τ := (geometricFiberProjUpperStarFrobeniusIso Λ f).hom) M N
  rw [Functor.LaxMonoidal.comp_μ, Category.assoc] at h
  rw [← cancel_epi (μ (upperStar Λ f.geometricGaloisFrobenius.hom) _ _ ≫
    (upperStar Λ f.geometricGaloisFrobenius.hom).map (μ (upperStar Λ f.geometricFiberProj) M N))]
  simp only [Category.assoc]
  rw [h, ← Functor.map_comp_assoc, Functor.Monoidal.μ_δ, Functor.map_id, Category.id_comp,
    Functor.Monoidal.μ_δ_assoc]

/-- **The Weil law of a tensor product of trivializations**: if the trivializations
`e : p^* M ≅ 𝟙` and `e' : p^* M' ≅ 𝟙` satisfy the Weil laws with scalars `N` and `N'`, the
induced trivialization of `p^* (M ⊗ M')` satisfies it with the scalar `N N'`. -/
lemma purity_mapTensorObjIsoUnit_weil
    {M M' : Mod (Sheaf (ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀)}
    (e : (upperStar Λ f.geometricFiberProj).obj M ≅ 𝟙_ _)
    (e' : (upperStar Λ f.geometricFiberProj).obj M' ≅ 𝟙_ _) (N N' : ℤ)
    (he : N • ((geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app M ≫ e.hom) =
      (upperStar Λ f.geometricGaloisFrobenius.hom).map e.hom ≫
        η (upperStar Λ f.geometricGaloisFrobenius.hom))
    (he' : N' • ((geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app M' ≫ e'.hom) =
      (upperStar Λ f.geometricGaloisFrobenius.hom).map e'.hom ≫
        η (upperStar Λ f.geometricGaloisFrobenius.hom)) :
    (N * N') • ((geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app (M ⊗ M') ≫
        (Functor.mapTensorObjIsoUnit (upperStar Λ f.geometricFiberProj) e e').hom) =
      (upperStar Λ f.geometricGaloisFrobenius.hom).map
          (Functor.mapTensorObjIsoUnit (upperStar Λ f.geometricFiberProj) e e').hom ≫
        η (upperStar Λ f.geometricGaloisFrobenius.hom) := by
  simp only [Functor.mapTensorObjIsoUnit, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
    tensorIso, Functor.map_comp, Category.assoc]
  rw [purity_geometricFiberProjUpperStarFrobeniusIso_hom_app_tensorObj]
  simp only [Category.assoc]
  rw [Functor.Monoidal.μ_δ_assoc, tensorHom_comp_tensorHom, ← Preadditive.comp_zsmul,
    ← Preadditive.comp_zsmul, ← Preadditive.zsmul_comp, ← purity_zsmul_tensorHom_zsmul, he, he',
    ← tensorHom_comp_tensorHom, Functor.OplaxMonoidal.δ_natural_assoc,
    Functor.OplaxMonoidal.purity_δ_unit_comp_tensorHom_η_comp_leftUnitor_hom]

end Monoidal

/-! ### The trivializations of `p^* ℚ̄_ℓ(d)` -/

section Powers

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
  {X₀ : Scheme.{u}} (a : X₀ ⟶ Spec (.of k)) {ζ : ℕ → AlgebraicClosure k}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

attribute [local instance] Mod.extendScalarsMonoidal

/-- The trivialization `p^* ℚ̄_ℓ(1) ≅ 𝟙` of the Tate twist on the geometric fibre. -/
noncomputable def purity_tateTwistOneTrivializationUnit :
    (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (tateTwistOne X₀ ℓ) ≅ 𝟙_ _ :=
  purityTateTwistOneTrivialization a hζ hζ' ≪≫ Functor.mapUnitIsoUnit _

/-- The Weil law of `purity_tateTwistOneTrivializationUnit`, with the scalar `q`. -/
theorem purity_tateTwistOneTrivializationUnit_weil :
    (Nat.card k : ℤ) •
        ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app
            (tateTwistOne X₀ ℓ) ≫ (purity_tateTwistOneTrivializationUnit a hζ hζ').hom) =
      (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          (purity_tateTwistOneTrivializationUnit a hζ hζ').hom ≫
        η (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧ := by
  simp only [purity_tateTwistOneTrivializationUnit, Functor.mapUnitIsoUnit, Iso.trans_hom,
    Iso.symm_hom, Functor.Monoidal.εIso_inv, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((geometricFiberProjUpperStarFrobeniusIso _ a).hom.app _)
    (purityTateTwistOneTrivialization a hζ hζ').hom, ← Preadditive.zsmul_comp,
    purityTateTwistOneTrivialization_weil, Category.assoc,
    purity_geometricFiberProjUpperStarFrobeniusIso_hom_app_unit_comp_η]

/-- The trivializations `p^* ℚ̄_ℓ(d) ≅ 𝟙`, `d ≥ 0`, of the tensor powers of `ℚ̄_ℓ(1)` on the
geometric fibre. -/
noncomputable def purity_tateTwistNatTrivialization :
    (d : ℕ) → (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (tateTwistNat X₀ ℓ d) ≅
      𝟙_ _
  | 0 => Functor.mapUnitIsoUnit _
  | d + 1 => Functor.mapTensorObjIsoUnit _ (purity_tateTwistNatTrivialization d)
      (purity_tateTwistOneTrivializationUnit a hζ hζ')

/-- **The Weil law of the trivialized Tate twists**: `q^d` times the canonical Weil structure of
`p^* ℚ̄_ℓ(d)` followed by the trivialization is `Fr^*` of the trivialization followed by the unit
comparison of `Fr^*`. -/
theorem purity_tateTwistNatTrivialization_weil : ∀ d : ℕ,
    ((Nat.card k : ℤ) ^ d) •
        ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app
            (tateTwistNat X₀ ℓ d) ≫ (purity_tateTwistNatTrivialization a hζ hζ' d).hom) =
      (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          (purity_tateTwistNatTrivialization a hζ hζ' d).hom ≫
        η (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧
  | 0 => by
    simp only [purity_tateTwistNatTrivialization, Functor.mapUnitIsoUnit, Iso.symm_hom,
      Functor.Monoidal.εIso_inv, pow_zero, one_smul]
    exact purity_geometricFiberProjUpperStarFrobeniusIso_hom_app_unit_comp_η _ a
  | d + 1 => by
    rw [pow_succ]
    exact purity_mapTensorObjIsoUnit_weil _ a _ _ _ _ (purity_tateTwistNatTrivialization_weil d)
      (purity_tateTwistOneTrivializationUnit_weil a hζ hζ')

/-- The trivialization `p^* ℚ̄_ℓ(d) ≅ p^* ℚ̄_ℓ` with values in the pulled-back unit. -/
noncomputable def purity_tateTwistNatTrivialization' (d : ℕ) :
    (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (tateTwistNat X₀ ℓ d) ≅
      (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (𝟙_ _) :=
  purity_tateTwistNatTrivialization a hζ hζ' d ≪≫
    Functor.Monoidal.εIso (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧

/-- **The Weil law of the trivialized Tate twists**, with values in `p^* ℚ̄_ℓ` and its canonical
Weil structure: `q^d • (S_{ℚ̄_ℓ(d)} ≫ e_d) = Fr^* e_d ≫ S_𝟙`. -/
theorem purity_tateTwistNatTrivialization'_weil (d : ℕ) :
    ((Nat.card k : ℤ) ^ d) •
        ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app
            (tateTwistNat X₀ ℓ d) ≫ (purity_tateTwistNatTrivialization' a hζ hζ' d).hom) =
      (a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          (purity_tateTwistNatTrivialization' a hζ hζ' d).hom ≫
        (geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app
          (𝟙_ _) := by
  have h := purity_geometricFiberProjUpperStarFrobeniusIso_hom_app_unit_comp_η
    (Profinite.padicAlgClRingObj ℓ) a
  rw [← cancel_mono (η (a.geometricFiberProj)^*⟦Profinite.padicAlgClRingObj ℓ⟧), Category.assoc, h,
    ← Functor.map_comp_assoc, Preadditive.zsmul_comp]
  simp only [purity_tateTwistNatTrivialization', Iso.trans_hom, Functor.Monoidal.εIso_hom,
    Category.assoc, Functor.Monoidal.ε_η, Category.comp_id]
  exact purity_tateTwistNatTrivialization_weil a hζ hζ' d

/-- **The Weil law in the pushforward convention**: for the Weil structures
`(Fr⁻¹)_* p^* M ≅ p^* M` of `AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilLowerStar`,
`q^d • ((Fr⁻¹)_* e_d⁻¹ ≫ S'_{ℚ̄_ℓ(d)}) = S'_𝟙 ≫ e_d⁻¹`. -/
theorem purity_tateTwistNatTrivialization'_weil_lowerStar (d : ℕ) :
    ((Nat.card k : ℤ) ^ d) •
        ((a.geometricGaloisFrobenius.inv)_*⟦Profinite.padicAlgClRingObj ℓ⟧.map
            (purity_tateTwistNatTrivialization' a hζ hζ' d).inv ≫
          (geometricFiberProjLowerStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app
            (tateTwistNat X₀ ℓ d)) =
      (geometricFiberProjLowerStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ) a).hom.app
          (𝟙_ _) ≫ (purity_tateTwistNatTrivialization' a hζ hζ' d).inv := by
  have h := purity_tateTwistNatTrivialization'_weil a hζ hζ' d
  have hnat := (upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj ℓ)
    a.geometricGaloisFrobenius).inv.naturality (purity_tateTwistNatTrivialization' a hζ hζ' d).inv
  simp only [geometricFiberProjLowerStarFrobeniusIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerLeft_app, Category.assoc]
  rw [reassoc_of% hnat, ← Preadditive.comp_zsmul]
  congr 1
  rw [← cancel_epi ((a.geometricGaloisFrobenius.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
    (purity_tateTwistNatTrivialization' a hζ hζ' d).hom), Preadditive.comp_zsmul,
    ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp,
    ← cancel_mono (purity_tateTwistNatTrivialization' a hζ hζ' d).hom, Preadditive.zsmul_comp,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, h]

end Powers

end AlgebraicGeometry.ProEtale.CondensedRing
