/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverComparisons
import WeilConjectures.AlgebraicGeometry.TotalTensorOverEquivIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Transport of ordinary evaluation across the open-site equivalence

This is a statement about actual complexes only. It mentions neither RHom nor
canonical derived evaluation nor an arbitrary derived representative.

## References

* Stacks Project, Tags 08DL, 08DJ and 08DQ.
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

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

section TransportProofs

private noncomputable local instance transportSchemeTensor (X : Scheme.{u}) :
    MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf

private theorem hom_quasiIso_over_transport (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ)
    (hhom : ∀ (M N : CochainComplex (localEvaluationModules X U) ℤ) (a : M ⟶ N),
      QuasiIso a → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map a))
    (b : ∀ M : CochainComplex (localEvaluationModules X U) ℤ,
      ((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj
          (homComplex (R := X.sheaf.over U) P M) ≅
        homComplex (R := U.toScheme.sheaf)
          (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj M))
    (hb : ∀ (M N : CochainComplex (localEvaluationModules X U) ℤ) (a : M ⟶ N),
      ((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).map
          (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map a) ≫ (b N).hom =
        (b M).hom ≫ ((homComplexFunctor (R := U.toScheme.sheaf)).obj
          (op (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj P))).map
            (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).map a)) :
    let T := (Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)
    ∀ (M N : CochainComplex (SheafOfModules.{u}
        U.toScheme.ringCatSheaf) ℤ) (a : M ⟶ N),
      QuasiIso a → QuasiIso
        (((homComplexFunctor (R := U.toScheme.sheaf)).obj (op (T.obj P))).map a) := by
  let : (Scheme.Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let E := (Scheme.Modules.overEquiv U).mapHomologicalComplex (.up ℤ)
  let T := E.functor
  let G := E.inverse
  let H := (homComplexFunctor (R := X.sheaf.over U)).obj (op P)
  let H' := (homComplexFunctor (R := U.toScheme.sheaf)).obj (op (T.obj P))
  dsimp only
  intro M N a ha
  let : QuasiIso a := ha
  have hg : QuasiIso (G.map a) := by
    change QuasiIso (((Scheme.Modules.overEquiv U).inverse.mapHomologicalComplex (.up ℤ)).map a)
    infer_instance
  have : QuasiIso (H.map (G.map a)) := hhom _ _ _ hg
  have : QuasiIso (T.map (H.map (G.map a))) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology (H.map (G.map a))
      (Scheme.Modules.overEquiv U).functor
  have : QuasiIso (H'.map (T.map (G.map a))) :=
    quasiIso_of_arrow_mk_iso (T.map (H.map (G.map a))) (H'.map (T.map (G.map a)))
      (Arrow.isoMk' _ _ (b (G.obj M)) (b (G.obj N)) (hb _ _ (G.map a)).symm)
  exact quasiIso_of_arrow_mk_iso (H'.map (T.map (G.map a))) (H'.map a)
    (Arrow.isoMk' _ _ (H'.mapIso (E.counitIso.app M)) (H'.mapIso (E.counitIso.app N)) (by
      change H'.map (E.counitIso.app M).hom ≫ H'.map a =
        H'.map (T.map (G.map a)) ≫ H'.map (E.counitIso.app N).hom
      rw [← H'.map_comp, ← H'.map_comp]
      exact congrArg H'.map (E.counitIso.hom.naturality a).symm))

private noncomputable local instance transportOverPreadditive (X : Scheme.{u}) (U : X.Opens) :
    MonoidalPreadditive (localEvaluationModules X U) :=
  Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1

private noncomputable local instance transportSchemePreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1

private theorem kFlat_over_transport (X : Scheme.{u}) (U : X.Opens)
    (K : CochainComplex (localEvaluationModules X U) ℤ)
    (D : CochainComplex (SheafOfModules.{u} U.toScheme.ringCatSheaf) ℤ)
    (d : ((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K ≅ D)
    (hK : K.IsKFlatTensor)
    (ht : ∀ A : CochainComplex (localEvaluationModules X U) ℤ,
      Nonempty (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor A K (curriedTensor _)) ≅
        CochainComplex.mapBifunctor
          (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj A)
          (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K)
          (curriedTensor _))) : D.IsKFlatTensor := by
  let : (Scheme.Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let E := (Scheme.Modules.overEquiv U).mapHomologicalComplex (.up ℤ)
  let T := E.functor
  intro A hA
  let G := E.inverse.obj A
  have hG : G.Acyclic := hA.map (Scheme.Modules.overEquiv U).inverse
  have htot := (hK G hG).map (Scheme.Modules.overEquiv U).functor
  obtain ⟨e⟩ := ht G
  let eA := (((curriedTensor
    (SheafOfModules.{u} U.toScheme.ringCatSheaf)).map₂CochainComplex).mapIso
      (E.counitIso.app A)).app (T.obj K)
  let eD := (((curriedTensor
    (SheafOfModules.{u} U.toScheme.ringCatSheaf)).map₂CochainComplex).obj A).mapIso d
  intro i
  exact (((htot i).of_iso e).of_iso eA).of_iso eD

private theorem kInjective_over_transport (X : Scheme.{u}) (U : X.Opens)
    (F : CochainComplex (localEvaluationModules X U) ℤ) [F.IsKInjective] :
    CochainComplex.IsKInjective
      (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj F) := by
  let : (Scheme.Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  infer_instance


end TransportProofs

set_option maxHeartbeats 600000 in
-- Comparing the site carriers and the chosen Hom functors needs extra elaboration steps.
/-- Transport the ordinary tensor and Hom models, and their component equation
(Stacks, Tags 08DL, 08DJ and 08DQ). -/
theorem exists_ordinaryEvaluation_over_transport (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (hdual : (localEvaluationDual X U P).IsKFlatTensor)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (hf : IsLocalOrdinaryEvaluation X U P F f) [F.IsKInjective] :
    let L := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    let P' := T.obj P
    let F' := T.obj F
    let O' := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
    let D' := homComplex (R := U.toScheme.sheaf) P' O'
    ∃ t : T.obj (localEvaluationTensor X U P F) ≅ pullbackTensorTotal U.toScheme F' D',
      ∃ b : T.obj (homComplex (R := X.sheaf.over U) P F) ≅
          homComplex (R := U.toScheme.sheaf) P' F',
        (∀ (M M' : CochainComplex
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ) (a : M ⟶ M'),
          QuasiIso a →
            QuasiIso (((homComplexFunctor (R := U.toScheme.sheaf)).obj (op P')).map a)) ∧
        D'.IsKFlatTensor ∧ CochainComplex.IsKInjective F' ∧
        IsSchemeOrdinaryEvaluation U.toScheme P' F' (t.inv ≫ T.map f ≫ b.hom) := by
  dsimp only
  obtain ⟨b, hb, d, ht⟩ := exists_ordinaryEvaluation_over_comparisons X U P
  obtain ⟨t, ht⟩ := ht F
  refine ⟨t, b F, hom_quasiIso_over_transport X U P hhom b hb, ?_, ?_, ht f hf⟩
  · exact kFlat_over_transport X U (localEvaluationDual X U P) _ d hdual
      (fun A ↦ exists_totalTensor_overEquiv_iso X U A (localEvaluationDual X U P))
  · exact kInjective_over_transport X U F

end AlgebraicGeometry
