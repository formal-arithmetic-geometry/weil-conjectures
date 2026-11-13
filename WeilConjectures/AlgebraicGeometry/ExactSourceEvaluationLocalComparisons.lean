/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.CanonicalEvaluationOpenRestriction
import WeilConjectures.AlgebraicGeometry.ExactSourceEvaluationOpenModels

/-! # The local representative equation for evaluation with an exact Hom source

Source: Stacks Project, Tags 08DL, 08DM and 08DQ, the ordinary complex models;
Tag 08DJ, the tensor-Hom representative equation.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem descend_comparison_squares
    {C D : Type*} [Category* C] [Category* D]
    (E : C ⥤ D) [E.Full] [E.Faithful]
    {S T S' T' : C} {A B : D} (g : S ⟶ T) (f : S' ⟶ T')
    (c : E.obj S ≅ A) (d : E.obj T ≅ B)
    (a : A ≅ E.obj S') (b : B ≅ E.obj T') (h : A ⟶ B)
    (h₁ : E.map g ≫ d.hom = c.hom ≫ h)
    (h₂ : h ≫ b.hom = a.hom ≫ E.map f) :
    ∃ a' : S ≅ S', ∃ b' : T ≅ T', g ≫ b'.hom = a'.hom ≫ f := by
  refine ⟨E.preimageIso (c ≪≫ a), E.preimageIso (d ≪≫ b), ?_⟩
  apply E.map_injective
  simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage,
    Iso.trans_hom]
  calc
    E.map g ≫ d.hom ≫ b.hom = c.hom ≫ h ≫ b.hom := by
      simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ b.hom) h₁
    _ = (c.hom ≫ a.hom) ≫ E.map f := by
      simpa only [Category.assoc] using congrArg (fun t ↦ c.hom ≫ t) h₂

set_option maxHeartbeats 600000 in
-- Derived equivalence instance comparisons need a larger declaration-local budget.
/-- The representative equation needs preservation of quasi-isomorphisms by Hom(P,-)
and K-flatness of its ordinary dual, rather than finite freeness or invertibility
of ordinary evaluation. The second complex is arbitrary (Stacks, Tags 08DL, 08DM, 08DQ and 08DJ). -/
theorem exists_exactSource_evaluation_local_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (_hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (_hdual : (localEvaluationDual X U P).IsKFlatTensor)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    HasDerivedCategory.standard _
  let ec := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U))
  have : ec.Additive := Functor.additive_of_preserves_binary_products ec
  let E := ec.mapDerivedCategory
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory
  obtain ⟨c, d, hrestrict⟩ := exists_canonicalEvaluation_open_restriction X U K N
  obtain ⟨aU, bU, hmodel⟩ := exists_exactSource_evaluation_open_models X U
    (E.obj (R.obj K)) (E.obj (R.obj N)) P F _hhom _hdual
    (E.mapIso _eK).symm (E.mapIso _eN).symm f _hf
  exact descend_comparison_squares E _ _ c d aU bU _ hrestrict hmodel

end AlgebraicGeometry
