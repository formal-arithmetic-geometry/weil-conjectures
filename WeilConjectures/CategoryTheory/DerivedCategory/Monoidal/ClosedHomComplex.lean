/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHomBidual
public import WeilConjectures.CategoryTheory.Monoidal.Closed.DualFullyFaithful
public import Mathlib.CategoryTheory.Localization.Opposite
public import WeilConjectures.CategoryTheory.Monoidal.Closed.InternalHomAdditive

/-!
# The derived internal hom into a K-injective complex is the hom complex

Let `C` be a monoidal closed Grothendieck abelian category as in
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`, so that `D(C)` is monoidal
closed, and let `I` be a K-injective complex. The internal hom `RHom(-, Q I)` of `D(C)` is defined
through a noncanonical choice of representatives, and its functoriality in the first variable
by uniqueness of adjoints. This file identifies it, as a functor `D(C)ᵒᵖ ⥤ D(C)`, with the derived
hom of hom complexes into `I` (`DerivedCategory.bifunctorRHomOfComplex`) for the internal hom
bifunctor of `C`: on a complex `K` both are `Q Hom(K, I)`
(`DerivedCategory.qhInternalHomToIhom`).

## Main results

- `DerivedCategory.precompQuasiIso_internalHom`: precomposition with a quasi-isomorphism is a
  quasi-isomorphism of internal hom complexes into `I`.
- `DerivedCategory.bifunctorRHomOfComplexIsoIhom`: the natural isomorphism
  `RHom_H(-, I) ≅ RHom(-, Q I)` of functors `D(C)ᵒᵖ ⥤ D(C)`, for `H` the internal hom of `C`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Opposite
open MonoidalClosed hiding assoc id_comp comp_id

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

omit [HasZeroObject C] [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
/-- The hom complex of the internal hom bifunctor is the internal hom complex. -/
lemma bifunctorHomObj_internalHom (K Y : CochainComplex C ℤ) :
    bifunctorHomObj MonoidalClosed.internalHom K Y = internalHomObj K Y :=
  rfl

/-- Precomposition on hom complexes of the internal hom bifunctor is `internalHomPre`. -/
lemma bifunctorHomMapLeft_internalHom {K K' : CochainComplex C ℤ} (f : K ⟶ K')
    (Y : CochainComplex C ℤ) :
    bifunctorHomMapLeft (H := MonoidalClosed.internalHom) (Y := Y) f = internalHomPre f Y := by
  ext n p q h
  exact (bifunctorHomMapLeft_f_π _ n p q h).trans (internalHomPre_f_π f Y n p q h).symm

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{v} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [(HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]
  (I : CochainComplex C ℤ) [I.IsKInjective]

open HomotopyCategory in
/-- The identification `Q Hom(K, I) ≅ RHom(Q K, Q I)` of the internal hom complex into a
K-injective complex with the derived internal hom: `qhInternalHomToIhom` read through
`quotientCompQhIso`. -/
noncomputable def qInternalHomIsoIhom (K : CochainComplex C ℤ) :
    Q.obj (CochainComplex.internalHomObj K I) ≅ (ihom (Q.obj K)).obj (Q.obj I) :=
  ((quotientCompQhIso C).app _).symm ≪≫ asIso (qhInternalHomToIhom K I) ≪≫
    (MonoidalClosed.preIso _ ((quotientCompQhIso C).app K).symm) ≪≫
      (ihom (Q.obj K)).mapIso ((quotientCompQhIso C).app I)
lemma qInternalHomIsoIhom_hom_naturality {K K' : CochainComplex C ℤ} (f : K ⟶ K') :
    Q.map (CochainComplex.internalHomPre f I) ≫ (qInternalHomIsoIhom I K).hom =
      (qInternalHomIsoIhom I K').hom ≫ (pre (Q.map f)).app (Q.obj I) := by
  have h₁ := (quotientCompQhIso C).inv.naturality (CochainComplex.internalHomPre f I)
  have h₂ := (quotientCompQhIso C).inv.naturality f
  dsimp at h₁ h₂
  simp only [qInternalHomIsoIhom, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    asIso_hom, Functor.mapIso_hom, preIso_hom, assoc]
  rw [reassoc_of% h₁, reassoc_of% (qhInternalHomToIhom_naturality f I),
    (pre (Q.map f)).naturality, ← NatTrans.comp_app_assoc, ← pre_map,
    ← NatTrans.comp_app_assoc, ← pre_map, h₂]

/-- Precomposition with a quasi-isomorphism is a quasi-isomorphism of internal hom complexes into
a K-injective complex: through `qInternalHomIsoIhom` it is precomposition in `D(C)` with an
isomorphism. -/
lemma precompQuasiIso_internalHom : PrecompQuasiIso MonoidalClosed.internalHom I := by
  intro K L a _
  rw [CochainComplex.bifunctorHomMapLeft_internalHom, ← isIso_Q_map_iff_quasiIso]
  have : IsIso ((pre (Q.map a)).app (Q.obj I)) :=
    inferInstanceAs (IsIso (preIso (Q.obj I) (asIso (Q.map a))).hom)
  have : IsIso (Q.map (CochainComplex.internalHomPre a I) ≫ (qInternalHomIsoIhom I K).hom) := by
    rw [qInternalHomIsoIhom_hom_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (qInternalHomIsoIhom I K).hom

/-- **The derived internal hom into a K-injective complex is the hom complex**: the derived hom
`RHom_H(-, I)` of hom complexes into `I`, for the internal hom bifunctor `H` of `C`, is the
internal hom `RHom(-, Q I)` of the monoidal closed category `D(C)`. On a complex `K` it is
`RHom_H(Q K, I) ≅ Q Hom(K, I) ≅ RHom(Q K, Q I)` (`bifunctorRHomOfComplexIsoIhom_hom_app_Q_obj`). -/
noncomputable def bifunctorRHomOfComplexIsoIhom :
    bifunctorRHomOfComplex MonoidalClosed.internalHom I ≅
      MonoidalClosed.internalHom.flip.obj (Q.obj I) :=
  Localization.liftNatIso Q.op (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).op
    (Q.op ⋙ bifunctorRHomOfComplex MonoidalClosed.internalHom I)
    (Q.op ⋙ MonoidalClosed.internalHom.flip.obj (Q.obj I)) _ _
    (NatIso.ofComponents
      (fun K ↦ bifunctorRHomOfComplexQObjIso _ (precompQuasiIso_internalHom I) K.unop ≪≫
        qInternalHomIsoIhom I K.unop) (fun {K K'} f ↦ by
          have h₁ := bifunctorRHomOfComplexQObjIso_hom_naturality
            (precompQuasiIso_internalHom I) f.unop
          rw [CochainComplex.bifunctorHomMapLeft_internalHom] at h₁
          dsimp
          rw [reassoc_of% h₁, qInternalHomIsoIhom_hom_naturality, assoc]
          rfl))

lemma bifunctorRHomOfComplexIsoIhom_hom_app_Q_obj (K : CochainComplex C ℤ) :
    (bifunctorRHomOfComplexIsoIhom I).hom.app (op (Q.obj K)) =
      (bifunctorRHomOfComplexQObjIso _ (precompQuasiIso_internalHom I) K).hom ≫
        (qInternalHomIsoIhom I K).hom := by
  dsimp only [bifunctorRHomOfComplexIsoIhom, Localization.liftNatIso]
  erw [Localization.liftNatTrans_app _ _ _ _ _ _ _ (op K)]
  simp

end DerivedCategory
