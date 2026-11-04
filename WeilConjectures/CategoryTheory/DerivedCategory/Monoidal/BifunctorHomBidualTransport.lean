/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedHomComplex
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Biduality of hom complexes from biduality in a monoidal closed derived category

Let `A` be an abelian category with a bifunctor `H : Aᵒᵖ ⥤ A ⥤ A` and an evaluation `E` satisfying
the triangle identity (`CochainComplex.BifunctorEvaluation.IsSelfDual`), as the internal hom and
the biduality maps of modules do. Let `U : A ⥤ B` be an additive equivalence to a monoidal closed
Grothendieck abelian category `B` whose derived category `D(B)` is monoidal closed, carrying `H`
to the internal hom of `B` (`CochainComplex.BifunctorMapIso`). Let `I` be a complex of `A` with
`U I` K-injective, and `W = Q (U I)`.

The derived hom `G = RHom_H(-, I)` of hom complexes is carried by `U` to the internal hom
`RHom(-, W)` of `D(B)` (`DerivedCategory.bifunctorRHomOfComplexMapIso`). Only the internal homs,
as functors, are compared: neither the evaluation nor the braiding of `D(B)`. Since the
double-dual morphism `δ : 𝟭 ⟶ G G` satisfies the triangle identity, `δ_K` is an isomorphism as soon
as `G` is fully faithful on `K` and `G G K` (`CategoryTheory.Functor.IsSelfDualUnit`). Full
faithfulness can be read in `D(B)`, where it is the full faithfulness of `RHom(-, W)`, a
consequence of Verdier biduality in `D(B)`
(`CategoryTheory.MonoidalClosed.bijective_pre_app_of_isIso`).

## Main results

- `DerivedCategory.precompQuasiIso_of_bifunctorMapIso`: precomposition with a quasi-isomorphism is
  a quasi-isomorphism of hom complexes into `I`.
- `DerivedCategory.bifunctorRHomOfComplexMapIso`: `U (RHom_H(K, I)) ≅ RHom(U K, W)`, naturally in
  `K`.
- `DerivedCategory.quasiIso_bifunctorHomBidual_of_bijective`: if `f ↦ RHom(f, W)` is bijective on
  a class of objects of `D(B)` stable under `RHom(-, W)` and containing `U K`, the double-dual
  morphism `K ⟶ Hom(Hom(K, I), I)` of hom complexes is a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Opposite CochainComplex
open MonoidalClosed hiding assoc id_comp comp_id

universe v u v' u'

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
  [Abelian.HasKInjectiveResolutions A] [HasCountableProducts A]
  {H : Aᵒᵖ ⥤ A ⥤ A} [H.Additive] [∀ M, (H.obj M).Additive]
  {B : Type u'} [Category.{v'} B] [Abelian B] [IsGrothendieckAbelian.{v'} B]
  [HasDerivedCategory.{v'} B]
  [MonoidalCategory B] [MonoidalClosed B] [MonoidalPreadditive B]
  [∀ (X₁ X₂ : GradedObject ℤ B), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [(HomotopyCategory.quasiIso B
    (ComplexShape.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]
  {U : A ⥤ B} [U.Additive] [U.IsEquivalence]
  [∀ n : ℤ, PreservesLimitsOfShape (Discrete (HomComplex.Triplet n)) U]
  (φ : BifunctorMapIso H MonoidalClosed.internalHom U)
  (I : CochainComplex A ℤ) [CochainComplex.IsKInjective ((U.mapHomologicalComplex _).obj I)]

set_option quotPrecheck false in
local notation "Uc" => U.mapHomologicalComplex (ComplexShape.up ℤ)

omit [HasDerivedCategory A] [Abelian.HasKInjectiveResolutions A] in
include φ in
/-- Precomposition with a quasi-isomorphism is a quasi-isomorphism of hom complexes into `I`: `U`
carries it to precomposition on internal hom complexes into the K-injective complex `U I`. -/
lemma precompQuasiIso_of_bifunctorMapIso : PrecompQuasiIso H I := by
  intro K L a _
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ U]
  have h := map_bifunctorHomMapLeft_comp_bifunctorHomObjMapIso_hom (Y := I) φ a
  have : QuasiIso ((Uc).map a) := inferInstance
  have := precompQuasiIso_internalHom ((Uc).obj I) ((Uc).map a)
  have : QuasiIso ((Uc).map (bifunctorHomMapLeft (H := H) (Y := I) a) ≫
      (bifunctorHomObjMapIso K I φ).hom) := by
    rw [h]
    infer_instance
  exact (quasiIso_iff_comp_right _ _).1 this

/-- The identification `U (Q Hom_H(K, I)) ≅ RHom(U (Q K), W)` of a hom complex with the internal hom
of `D(B)`, `W = Q (U I)`. -/
noncomputable def mapHomComplexIsoIhom (K : CochainComplex A ℤ) :
    U.mapDerivedCategory.obj (Q.obj (bifunctorHomObj H K I)) ≅
      (ihom (U.mapDerivedCategory.obj (Q.obj K))).obj (Q.obj ((Uc).obj I)) :=
  U.mapDerivedCategoryFactors.app _ ≪≫ Q.mapIso (bifunctorHomObjMapIso K I φ) ≪≫
    qInternalHomIsoIhom ((Uc).obj I) ((Uc).obj K) ≪≫
      preIso _ (U.mapDerivedCategoryFactors.app K)

omit [Abelian.HasKInjectiveResolutions A] in
lemma mapHomComplexIsoIhom_hom_naturality {K K' : CochainComplex A ℤ} (f : K ⟶ K') :
    U.mapDerivedCategory.map (Q.map (bifunctorHomMapLeft (H := H) (Y := I) f)) ≫
        (mapHomComplexIsoIhom φ I K).hom =
      (mapHomComplexIsoIhom φ I K').hom ≫
        (pre (U.mapDerivedCategory.map (Q.map f))).app (Q.obj ((Uc).obj I)) := by
  have h₁ := U.mapDerivedCategoryFactors.hom.naturality (bifunctorHomMapLeft (H := H) (Y := I) f)
  have h₂ := U.mapDerivedCategoryFactors.hom.naturality f
  have h₃ := map_bifunctorHomMapLeft_comp_bifunctorHomObjMapIso_hom (Y := I) φ f
  have h₄ := qInternalHomIsoIhom_hom_naturality ((Uc).obj I) ((Uc).map f)
  rw [← bifunctorHomMapLeft_internalHom] at h₄
  dsimp at h₁ h₂
  simp only [mapHomComplexIsoIhom, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, preIso_hom,
    assoc]
  rw [reassoc_of% h₁, ← Q.map_comp_assoc, h₃, Q.map_comp_assoc, reassoc_of% h₄,
    ← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map, h₂]

/-- **`U` carries the derived hom of hom complexes into `I` to the internal hom of `D(B)`**:
`U (RHom_H(K, I)) ≅ RHom(U K, W)`, `W = Q (U I)`, naturally in `K`. -/
noncomputable def bifunctorRHomOfComplexMapIso :
    bifunctorRHomOfComplex H I ⋙ U.mapDerivedCategory ≅
      U.mapDerivedCategory.op ⋙ MonoidalClosed.internalHom.flip.obj (Q.obj ((Uc).obj I)) :=
  Localization.liftNatIso Q.op (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).op
    (Q.op ⋙ bifunctorRHomOfComplex H I ⋙ U.mapDerivedCategory)
    (Q.op ⋙ U.mapDerivedCategory.op ⋙ MonoidalClosed.internalHom.flip.obj (Q.obj ((Uc).obj I)))
    _ _
    (NatIso.ofComponents
      (fun K ↦ U.mapDerivedCategory.mapIso (bifunctorRHomOfComplexQObjIso H
        (precompQuasiIso_of_bifunctorMapIso φ I) K.unop) ≪≫ mapHomComplexIsoIhom φ I K.unop)
      (fun {K K'} f ↦ by
        have h₁ := bifunctorRHomOfComplexQObjIso_hom_naturality
          (precompQuasiIso_of_bifunctorMapIso φ I) f.unop
        dsimp
        rw [← U.mapDerivedCategory.map_comp_assoc, h₁, U.mapDerivedCategory.map_comp_assoc,
          mapHomComplexIsoIhom_hom_naturality, assoc]
        rfl))

lemma bifunctorRHomOfComplexMapIso_hom_app_Q_obj (K : CochainComplex A ℤ) :
    (bifunctorRHomOfComplexMapIso φ I).hom.app (op (Q.obj K)) =
      U.mapDerivedCategory.map (bifunctorRHomOfComplexQObjIso H
        (precompQuasiIso_of_bifunctorMapIso φ I) K).hom ≫ (mapHomComplexIsoIhom φ I K).hom := by
  dsimp only [bifunctorRHomOfComplexMapIso, Localization.liftNatIso]
  erw [Localization.liftNatTrans_app _ _ _ _ _ _ _ (op K)]
  simp

include φ in
/-- **Biduality of hom complexes from the full faithfulness of the dual of `D(B)`.** Let `P` be a
class of objects of `D(B)`, closed under isomorphisms and under `RHom(-, W)`, `W = Q (U I)`, on
which `f ↦ RHom(f, W)` is bijective. Then for every complex `M` with `U M` in `P`, the double-dual
morphism `M ⟶ Hom(Hom(M, I), I)` of hom complexes is a quasi-isomorphism. -/
theorem quasiIso_bifunctorHomBidual_of_bijective (E : BifunctorEvaluation H) (hE : E.IsSelfDual)
    (P : ObjectProperty (DerivedCategory B)) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ X, P X → P ((ihom X).obj (Q.obj ((Uc).obj I))))
    (hbij : ∀ X Y, P X → P Y →
      Function.Bijective (fun f : X ⟶ Y ↦ (pre f).app (Q.obj ((Uc).obj I))))
    (M : CochainComplex A ℤ) (hM : P (U.mapDerivedCategory.obj (Q.obj M))) :
    QuasiIso (bifunctorHomBidual E M I) := by
  have hI := precompQuasiIso_of_bifunctorMapIso φ I
  rw [← isIso_bifunctorRHomBidual_app_Q_obj_iff E hI]
  have hV : U.mapDerivedCategory.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  have hG (X : DerivedCategory A) (hX : P (U.mapDerivedCategory.obj X)) :
      P (U.mapDerivedCategory.obj ((bifunctorRHomOfComplex H I).obj (op X))) :=
    P.prop_of_iso ((bifunctorRHomOfComplexMapIso φ I).app (op X)).symm (hP _ hX)
  have hbij' (T X : DerivedCategory A) (hT : P (U.mapDerivedCategory.obj T))
      (hX : P (U.mapDerivedCategory.obj X)) :
      Function.Bijective (fun f : T ⟶ X ↦ (bifunctorRHomOfComplex H I).map f.op) := by
    let a := (bifunctorRHomOfComplexMapIso φ I).app (op X)
    let b := (bifunctorRHomOfComplexMapIso φ I).app (op T)
    have key (f : T ⟶ X) : U.mapDerivedCategory.map ((bifunctorRHomOfComplex H I).map f.op) =
        a.hom ≫ (pre (U.mapDerivedCategory.map f)).app (Q.obj ((Uc).obj I)) ≫ b.inv := by
      rw [← cancel_mono b.hom, assoc, assoc, Iso.inv_hom_id, comp_id]
      exact (bifunctorRHomOfComplexMapIso φ I).hom.naturality f.op
    have : (fun f : T ⟶ X ↦ (bifunctorRHomOfComplex H I).map f.op) =
        hV.homEquiv.symm ∘ (a.symm.homCongr b.symm) ∘
          (fun g ↦ (pre g).app (Q.obj ((Uc).obj I))) ∘ hV.homEquiv := by
      funext f
      apply hV.map_injective
      rw [key]
      simp [Iso.homCongr_apply]
    rw [this]
    exact hV.homEquiv.symm.bijective.comp ((a.symm.homCongr b.symm).bijective.comp
      ((hbij _ _ hT hX).comp hV.homEquiv.bijective))
  exact (isSelfDualUnit_bifunctorRHomBidual E hI hE).isIso_app_of_bijective (Q.obj M)
    (hbij' _ _ hM hM) (hbij' _ _ (hG _ (hG _ hM)) hM)

end DerivedCategory
