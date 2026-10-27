/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.FiniteDerivedTensorModels

/-! # Identifying a tensor comparison by its normalized cochain square

Source: Stacks 07A4 and 0G7E. The cochain square is precisely the canonical
comparison's unique representative characterization, in the equivalent model interface.
(blueprint: lem-pur-canonical-cochain-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open CategoryTheory.CochainPullback CategoryTheory.RingedDerivedComparisons
open WeilConjectures

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 100000] HomologicalComplex.monoidalCategoryStruct
attribute [local irreducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
  SheafOfModules.monoidalCategory SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive SheafOfModules.siteSheafTensorRight
  DerivedCategory instCategoryDerivedCategory HomologicalComplex₂.total
  CategoryTheory.CochainPullback.comparison HomologicalComplex.single

namespace CategoryTheory.FiniteDerivedTensorModels

attribute [local irreducible] legacyComparison canonical_model
  SheafOfModules.RingedTensorEdge.tensorComparison
  SheafOfModules.ringedTopoiCanonicalDerivedTensorComparison

section NativeComparison

set_option maxHeartbeats 800000 in
-- Elaborate the full two-variable representative square in both tensor presentations.
/-- A normalized cochain square identifies the canonical comparison.
Source: Stacks 07A4 and 0G7E.
(blueprint: lem-pur-canonical-cochain-tensor-comparison).

Proof: rewrite the source and target restricted-model components by canonical_model_eq,
replace the homotopy counit components by the specified cochain components, and replace
the total inverse by the cochain comparison. The hypothesis is exactly the resulting
representative square. Uniqueness in ringedTopoiCanonicalDerivedTensorPullback gives
the equality of natural isomorphisms.
-/
theorem canonicalComparison_eq {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : CochainPullback.Comparison.{u, u, u, u, u} f)
    (F : Y.D ⥤ X.D)
    (εc : DerivedCategory.Q ⋙ F ⟶ CochainPullback.pull f ⋙ DerivedCategory.Q)
    (nu : Y.closed.tensor ⋙ F ≅ (F.prod F) ⋙ X.closed.tensor)
    (ε : DerivedCategory.Qh ⋙ F ⟶ f.L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso Y.modules (.up ℤ)))
    (heq : ∀ P : CochainComplex Y.modules ℤ,
      ε.app ((HomotopyCategory.quotient Y.modules (.up ℤ)).obj P) = εc.app P)
    [PreservesFiniteLimits f.uInv]
    (hnormalized : ∀ (P Q : CochainComplex Y.modules ℤ)
      (hP : Y.corner.mateFlat P) (hQ : Y.corner.mateFlat Q),
      ∃ (hP' : X.corner.mateFlat ((CochainPullback.pull f).obj P))
        (hQ' : X.corner.mateFlat ((CochainPullback.pull f).obj Q)),
        F.map (Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1).hom ≫
            nu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            X.closed.tensor.map (Prod.mkHom (εc.app P) (εc.app Q)) =
          εc.app (P ⊗ Q) ≫ DerivedCategory.Q.map (CochainPullback.comparison f k P Q).hom ≫
            (X.model.iso X.J X.A X.closed ((CochainPullback.pull f).obj P)
              ((CochainPullback.pull f).obj Q) hP'.1 hQ'.1).hom) :
    SheafOfModules.ringedTopoiCanonicalDerivedTensorComparison
      f.uInv f.uPush f.adj f.I f.coefficient f.L f.hobj f.hmap F ε hε
      Y.corner.mateFlat X.corner.mateFlat (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
      Y.closed.tensor X.closed.tensor (canonical_model Y).representative
      (canonical_model X).representative (legacyComparison f k) f.V f.moduleAdj = nu := by
  unfold SheafOfModules.ringedTopoiCanonicalDerivedTensorComparison
  let rY := canonical_model Y
  let rX := canonical_model X
  have hc (P : CochainComplex Y.modules ℤ) :
      derivedPullbackComplexComparison f.L F ε P = εc.app P :=
    (complexComparison_eq_component f.L F ε P).trans (heq P)
  have := f.finiteLimits
  have h := (Classical.choose_spec
    (SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback
      f.uInv f.uPush f.adj f.I f.coefficient f.L f.hobj f.hmap F ε hε
      Y.corner.mateFlat X.corner.mateFlat (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
      Y.closed.tensor X.closed.tensor rY.representative rX.representative
      (legacyComparison f k) f.V f.moduleAdj).2.exists)
  apply (SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback
    f.uInv f.uPush f.adj f.I f.coefficient f.L f.hobj f.hmap F ε hε
    Y.corner.mateFlat X.corner.mateFlat (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    Y.closed.tensor X.closed.tensor rY.representative rX.representative
    (legacyComparison f k) f.V f.moduleAdj).2.unique h
  intro P Q hP hQ
  obtain ⟨hp, hq, hh⟩ := hnormalized P Q hP hQ
  refine ⟨hp, hq, ?_⟩
  dsimp only [rY, rX]
  erw [canonical_model_eq Y P Q hP hQ,
    canonical_model_eq X _ _ hp hq]
  simp only [hc, Functor.mapIso_inv, legacy_comparison_eq]
  with_unfolding_all exact hh

end NativeComparison

end CategoryTheory.FiniteDerivedTensorModels
