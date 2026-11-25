/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedExtension
public import WeilConjectures.Algebra.Homology.System.SystemScalarDerivedExtension
public import WeilConjectures.Algebra.Homology.SmoothPurity.ExtensionEvaluationComparison
public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
public import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequence

/-! # Derived evaluation of subsequence extension

## References

* Stacks Project, Tags 03D7, 03EK, 06YT, 0FND
* Zheng 4.1
* Zheng, Construction 4.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r : ℕ ↪o ℕ) (m : ℕ)

omit [EssentiallySmall.{w} C] in
/-- The selected evaluation square is represented by the actual strict transition. -/
theorem systemSelectedDerivedSquare_rep (K : CochainComplex (StrictRingSystem B) ℤ) :
    ((systemDerivedSubsequenceEvaluation B r (systemNextSelected r m)).hom ≫
      systemDerivedTransition B (systemNextSelected_spec r m).1).app
        (DerivedCategory.Q.obj K) ≫
      (systemRestriction B (systemNextSelected_spec r m).1).mapDerivedCategory.map
        ((systemEvaluation B m).mapDerivedCategoryFactors.hom.app K) ≫
      (systemRestriction B (systemNextSelected_spec r m).1).mapDerivedCategoryFactors.hom.app
        (((systemEvaluation B m).mapHomologicalComplex (.up ℤ)).obj K) =
    (derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).map
        ((systemSubsequence B r).mapDerivedCategoryFactors.hom.app K) ≫
      (systemEvaluation (selectedSystemRings B r)
        (systemNextSelected r m)).mapDerivedCategoryFactors.hom.app
        (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((strictSystemTransition B (systemNextSelected_spec r m).1).mapHomologicalComplex
          (.up ℤ) |>.app K) := by
  simp only [NatTrans.comp_app, Category.assoc]
  rw [systemDerivedTransition_rep, ← Category.assoc,
    systemDerivedSubsequenceEvaluation_rep, Category.assoc]

/-- The ordinary selected comparison is the mate at the ordinary unit. -/
theorem systemSelectedOrdinaryUnitSquare
    (P : StrictRingSystem (selectedSystemRings B r)) :
    (systemTensorAdj S B (systemNextSelected_spec r m).1).homEquiv _ _
      ((systemSelectedBelow S T B r m).inv.app P) =
    (systemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).map
      ((systemSelectedAdjunction S T B r).unit.app P) ≫
      ((systemSelectedFunctor S T B r).obj P).transition (systemNextSelected_spec r m).1 := by
  have ht := systemSelectedTranspose S T B r m P
    ((systemSelectedFunctor S T B r).obj P) (𝟙 _)
  erw [(systemEvaluation B m).map_id, Category.comp_id,
    (systemSelectedAdjunction S T B r).homEquiv_unit,
    (systemSubsequence B r).map_id, Category.comp_id] at ht
  exact ht

/-- Derived subsequence extension evaluates as the derived tensor of the first
selected component above m. -/
def systemSelectedDerivedBelow (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) :
    (systemSelectedDerivedExtension B r S T).derived ⋙ derivedSystemEvaluation B m ≅
      derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m) ⋙
        systemDerivedTensor S B (systemNextSelected_spec r m).1 :=
  derivedExtensionEvaluationIso (systemSelectedDerivedExtension B r S T)
    (systemScalarModelExtension (S (B.map (homOfLE (systemNextSelected_spec r m).1).op)))
    (systemEvaluation (selectedSystemRings B r) (systemNextSelected r m))
    (systemEvaluation B m)
    (derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m))
    (systemEvaluation (selectedSystemRings B r)
        (systemNextSelected r m)).mapDerivedCategoryFactors
    ((systemDerivedSubsequenceEvaluation B r (systemNextSelected r m)).hom ≫
      systemDerivedTransition B (systemNextSelected_spec r m).1)
    (strictSystemTransition B (systemNextSelected_spec r m).1)
    (systemSelectedDerivedSquare_rep B r m)
    (systemSelectedBelow S T B r m).symm (systemSelectedOrdinaryUnitSquare S T B r m)
    (strictRingSystem_kFlatResolution (selectedSystemRings B r)) (fun _ hP ↦ (hP _).1)

/-- The selected derived comparison intertwines the actual normalized Hom transposes. -/
theorem systemSelectedDerivedTranspose
    (P : DerivedCategory (StrictRingSystem (selectedSystemRings B r)))
    (M : DerivedCategory (StrictRingSystem B))
    (f : (systemSelectedDerivedExtension B r S T).derived.obj P ⟶ M) :
    (systemDerivedTensorAdj S B (systemNextSelected_spec r m).1).homEquiv
      ((derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).obj P)
      ((derivedSystemEvaluation B m).obj M)
      ((systemSelectedDerivedBelow B r m S T).inv.app P ≫
        (derivedSystemEvaluation B m).map f) =
    (derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).map
      ((systemSelectedDerivedExtension B r S T).adjunction.homEquiv P M f) ≫
      (systemDerivedSubsequenceEvaluation B r (systemNextSelected r m)).hom.app M ≫
      (systemDerivedTransition B (systemNextSelected_spec r m).1).app M := by
  simpa only [systemSelectedDerivedBelow, systemScalarModelExtension,
    systemDerivedTensorAdj, NatTrans.comp_app, Category.assoc] using
    derivedExtensionEvaluationIso_transpose (systemSelectedDerivedExtension B r S T)
      (systemScalarModelExtension (S (B.map (homOfLE (systemNextSelected_spec r m).1).op)))
      (systemEvaluation (selectedSystemRings B r) (systemNextSelected r m))
      (systemEvaluation B m)
      (derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m))
      (systemEvaluation (selectedSystemRings B r)
        (systemNextSelected r m)).mapDerivedCategoryFactors
      ((systemDerivedSubsequenceEvaluation B r (systemNextSelected r m)).hom ≫
        systemDerivedTransition B (systemNextSelected_spec r m).1)
      (strictSystemTransition B (systemNextSelected_spec r m).1)
      (systemSelectedDerivedSquare_rep B r m)
      (systemSelectedBelow S T B r m).symm (systemSelectedOrdinaryUnitSquare S T B r m)
      (strictRingSystem_kFlatResolution (selectedSystemRings B r)) (fun _ hP ↦ (hP _).1) P M f

end SheafOfModules
