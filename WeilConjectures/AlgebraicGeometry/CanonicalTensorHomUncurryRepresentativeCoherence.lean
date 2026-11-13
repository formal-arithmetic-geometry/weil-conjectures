/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomIdentityEvaluationCoherence

/-! # Independence of the localized evaluation from a chain presentation

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

set_option maxHeartbeats 700000 in
-- Explicit functor identity rewrites elaborate through the sheaf and localization instances.
set_option backward.isDefEq.respectTransparency.types true in
private theorem localized_uncurry_input (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L M : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) :
    letI := schemeDerivedTensorMonoidal X
    pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
          schemeHomResolutionInverse X M =
      ((DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L)) ≫
        ((schemeDerivedInternalHomResolutionIso X L M).hom ⊗ₘ
          𝟙 (DerivedCategory.Q.obj L)) ≫
        pullbackTensorModelMap X _ L ≫
          DerivedCategory.Q.map (schemeTensorHomUncurry X _ L M (𝟙 _)) ≫
            schemeHomResolutionInverse X M := by
  let := schemeDerivedTensorMonoidal X
  have h := schemeTensorHomUncurry_localized_evaluation X _ P L L M M φ (𝟙 L) (𝟙 M)
    (𝟙 _)
  have hid : ((𝟙 L).op, (schemeHomKInjectiveResolution X).map (𝟙 M)) =
      𝟙 (op L, (schemeHomKInjectiveResolution X).obj M) := by
    rw [(schemeHomKInjectiveResolution X).map_id M, op_id]
    rfl
  have hφid : φ ≫ 𝟙 _ ≫
      (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map
        (X := (op L, (schemeHomKInjectiveResolution X).obj M))
        (Y := (op L, (schemeHomKInjectiveResolution X).obj M))
        ((𝟙 L).op, (schemeHomKInjectiveResolution X).map (𝟙 M)) = φ := by
    rw [hid, (Functor.uncurry.obj (homComplexFunctor (R := X.sheaf))).map_id]
    exact (congrArg (fun k ↦ φ ≫ k) (Category.comp_id (𝟙 _))).trans
      (Category.comp_id φ)
  rw [hφid, DerivedCategory.Q.map_id L, DerivedCategory.Q.map_id M] at h
  simp only [Category.comp_id] at h
  rw [h]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem evaluation_heq {C : Type*} [Category C] [MonoidalCategory C]
    (H : Cᵒᵖ × C ⥤ C) {K L M K' L' M' : C}
    (hK : K = K') (hL : L = L') (hM : M = M')
    (f : K ⟶ H.obj (op L, M)) (f' : K' ⟶ H.obj (op L', M'))
    (E : H.obj (op L, M) ⊗ L ⟶ M)
    (E' : H.obj (op L', M') ⊗ L' ⟶ M')
    (hf : HEq f f') (hE : HEq E E') :
    HEq ((f ⊗ₘ 𝟙 L) ≫ E) ((f' ⊗ₘ 𝟙 L') ≫ E') := by
  subst K'
  subst L'
  subst M'
  cases eq_of_heq hf
  cases eq_of_heq hE
  rfl

/-- Two chain presentations of the same literal derived input have the same localized
uncurried output. Object equalities and heterogeneous equalities record only transport
along equality, not transport along arbitrary isomorphisms. No family of functions is
asserted to exist here.
Source: Stacks Project, cohomology.tex, Tag 08DJ; sites-cohomology.tex, Tags 0A90, 0A96. -/
theorem tensorHomUncurry_representative_coherence (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L M P' L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hP' : P'.IsKFlatTensor)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (φ' : P' ⟶ homComplex (R := X.sheaf) L'
      ((schemeHomKInjectiveResolution X).obj M'))
    (hK : DerivedCategory.Q.obj P = DerivedCategory.Q.obj P')
    (hL : DerivedCategory.Q.obj L = DerivedCategory.Q.obj L')
    (hM : DerivedCategory.Q.obj M = DerivedCategory.Q.obj M')
    (hφ : HEq (DerivedCategory.Q.map φ ≫
        (schemeDerivedInternalHomResolutionIso X L M).inv)
      (DerivedCategory.Q.map φ' ≫
        (schemeDerivedInternalHomResolutionIso X L' M').inv)) :
    HEq (pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
          schemeHomResolutionInverse X M)
      (pullbackTensorModelMap X P' L' ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P' L' M' φ') ≫
          schemeHomResolutionInverse X M') := by
  have _ := hP
  have _ := hP'
  let := schemeDerivedTensorMonoidal X
  rw [localized_uncurry_input X P L M φ, localized_uncurry_input X P' L' M' φ']
  exact evaluation_heq
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf) hK hL hM _ _ _ _ hφ
    (tensorHomIdentityEvaluation_coherence X L M L' M' hL hM)

end AlgebraicGeometry
