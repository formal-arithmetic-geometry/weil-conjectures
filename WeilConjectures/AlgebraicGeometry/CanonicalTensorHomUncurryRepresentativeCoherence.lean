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

## References

* Stacks Project, Tags 08DJ, 0A90 and 0A96
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

private theorem localized_uncurry_factor_of_naturality
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    (H : Cᵒᵖ × C ⥤ C) (I : C ⥤ C) (Q : C ⥤ D) {P L M : C} {HD : D}
    (φ : P ⟶ H.obj (op L, I.obj M))
    (U : (P ⟶ H.obj (op L, I.obj M)) → (Q.obj P ⊗ Q.obj L ⟶ Q.obj M))
    (E : Q.obj (H.obj (op L, I.obj M)) ⊗ Q.obj L ⟶ Q.obj M)
    (j : HD ≅ Q.obj (H.obj (op L, I.obj M)))
    (h : U (φ ≫ 𝟙 _ ≫ H.map ((𝟙 L).op, I.map (𝟙 M))) =
      (Q.map φ ⊗ₘ Q.map (𝟙 L)) ≫ E ≫ Q.map (𝟙 M)) :
    U φ = ((Q.map φ ≫ j.inv) ⊗ₘ 𝟙 (Q.obj L)) ≫
      (j.hom ⊗ₘ 𝟙 (Q.obj L)) ≫ E := by
  have hid : ((𝟙 L).op, I.map (𝟙 M)) = 𝟙 (op L, I.obj M) := by
    rw [I.map_id, op_id]
    rfl
  rw [hid, H.map_id] at h
  simp only [Category.comp_id, Q.map_id] at h
  rw [h]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

-- Apply the categorical identity calculation without rewriting the concrete sheaf instances.
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
  exact localized_uncurry_factor_of_naturality
    (C := CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (Functor.uncurry.obj (homComplexFunctor.{u, u, u, u} (R := X.sheaf)))
    (schemeHomKInjectiveResolution X) DerivedCategory.Q φ
    (fun ψ ↦ pullbackTensorModelMap X P L ≫
      DerivedCategory.Q.map (schemeTensorHomUncurry X P L M ψ) ≫
        schemeHomResolutionInverse X M)
    _ (schemeDerivedInternalHomResolutionIso X L M)
    (schemeTensorHomUncurry_localized_evaluation X _ P L L M M φ (𝟙 L) (𝟙 M) (𝟙 _))

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
asserted to exist here (Stacks, Tags 08DJ, 0A90 and 0A96). -/
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
