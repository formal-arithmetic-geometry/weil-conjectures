/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Submission.WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Submission.WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherent
import Submission.WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import Submission.WeilConjectures.AlgebraicGeometry.SupportedPerfectFactorization

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Perfect annihilator for a map to a supported complex

Source: Stacks Project, perfect.tex, Tag 0A9C
(blueprint: lem-sc-pseudo-coherent-support-annihilation).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- The structure sheaf is perfect. -/
theorem isPerfect_tensorUnit (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    Scheme.IsPerfect X (𝟙_ (schemeDerivedCategory X)) := by
  intro x
  let R := (moduleRings X.toRingedSpace).over (⊤ : X.Opens)
  let K := (CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj
    (SheafOfModules.unit R)
  refine ⟨⊤, trivial, K, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨0, 0, ?_⟩
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro n
    by_cases hn : n = 0
    · subst n
      let e : K.X 0 ≅ SheafOfModules.free (R := R) (ULift.{u} (Fin 1)) :=
        (eqToIso (HomologicalComplex.single_obj_X_self _ _ _)) ≪≫
          (coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ SheafOfModules.unit R)).symm
      exact ⟨1, e.hom, e.inv, e.hom_inv_id⟩
    · have hz : IsZero (K.X n) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      exact ⟨0, 0, 0, by simpa using hz.eq_of_src (0 : K.X n ⟶ K.X n) (𝟙 _)⟩
  · let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) ⊤
    let eunit : 𝟙_ (schemeDerivedCategory X) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace)) :=
      (DerivedCategory.quotientCompQhIso _).app _
    exact ⟨F.mapDerivedCategory.mapIso eunit ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (SheafOfModules.unit R)⟩

end AlgebraicGeometry
