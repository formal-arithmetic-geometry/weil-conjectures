/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverTransport
import WeilConjectures.AlgebraicGeometry.KInjectiveSchemeEvaluationModels

/-! # K-injective models for evaluation on the open scheme

Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The standard localization is available on the open scheme independently of the
specified localization universe of the over-site.
Source: Stacks Project, Tag 05RU. -/
local instance kInjectiveEvaluationStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

set_option maxHeartbeats 1000000 in
-- Elaborating the transported models unfolds the exact-functor factorization.
/-- Ordinary representative evaluation when the coefficient complex is K-injective.
Source: Stacks Project, cohomology.tex, Tags 08DJ,
08DM (lemma-Rhom-strictly-perfect), and 08DQ (lemma-dual-perfect-complex). -/
theorem exists_exactSource_kInjective_evaluation_open_models (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory U.toScheme)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (_hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (_hdual : (localEvaluationDual X U P).IsKFlatTensor)
    (_eK : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj P) ≅ K)
    (_eN : (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj F) ≅ N)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) [F.IsKInjective] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let H := derivedInternalHom
      (Opens.grothendieckTopology U.toScheme.toRingedSpace) U.toScheme.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory U.toScheme))
    let g := ((schemeDerivedTensorHomEquiv U.toScheme) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv U.toScheme) D K
          (𝟙_ (schemeDerivedCategory U.toScheme)) (𝟙 D)) ≫ (ρ_ N).hom)
    ∃ a : N ⊗ D ≅ E.obj (DerivedCategory.Q.obj (localEvaluationTensor X U P F)),
      ∃ b : H.obj (op K, N) ≅
          E.obj (DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F)),
        g ≫ b.hom = a.hom ≫ E.map (DerivedCategory.Q.map f) := by
  let L := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  let T := L.mapHomologicalComplex (.up ℤ)
  let E := L.mapDerivedCategory
  let v := L.mapDerivedCategoryFactors
  obtain ⟨t, b, hhom, hdual, hF, hf⟩ :=
    exists_ordinaryEvaluation_over_transport X U P F _hhom _hdual f _hf
  have : CochainComplex.IsKInjective (T.obj F) := hF
  let eK : DerivedCategory.Q.obj (T.obj P) ≅ K := (v.app P).symm ≪≫ _eK
  let eN : DerivedCategory.Q.obj (T.obj F) ≅ N := (v.app F).symm ≪≫ _eN
  obtain ⟨a', b', h⟩ := exists_kInjective_scheme_evaluation_models U.toScheme K N
    (T.obj P) (T.obj F) hhom hdual eK eN (t.inv ≫ T.map f ≫ b.hom) hf
  refine ⟨a' ≪≫ (DerivedCategory.Q.mapIso t).symm ≪≫
    (v.app (localEvaluationTensor X U P F)).symm,
    b' ≪≫ (DerivedCategory.Q.mapIso b).symm ≪≫
      (v.app (homComplex (R := X.sheaf.over U) P F)).symm, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Functor.mapIso_inv, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, Category.comp_id]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc, Iso.app_inv, L, T] using
    congrArg (fun z ↦ a'.hom ≫ DerivedCategory.Q.map t.inv ≫ z) (v.inv.naturality f)

end AlgebraicGeometry
