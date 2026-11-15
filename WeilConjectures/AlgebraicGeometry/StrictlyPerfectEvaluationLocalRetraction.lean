/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectLocalHomComputations
import WeilConjectures.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation

/-! # A local retraction of canonical derived evaluation

## References

* Stacks Project, Cohomology of Sheaves, Tag 08DQ, proof of; Tags 08DM and 08DL.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
-- The localized module carriers and tensor-Hom expression need extra elaboration steps.
/-- A local retraction of canonical derived evaluation.
Only one inverse identity is asserted. No representative of N and no
comparison square with a prescribed ordinary chain map is part of the statement.
-/
theorem exists_strictlyPerfect_evaluation_local_retraction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ r : R.obj (H.obj (op K, N)) ⟶ R.obj (N ⊗ D),
      R.map g ≫ r = 𝟙 (R.obj (N ⊗ D)) := by
  classical
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory
  let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
    X.toRingedSpace.sheaf
  let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
  let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
    ((α_ N D K).hom ≫ N ◁
      ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
        (ρ_ N).hom)
  let Q := DerivedCategory.Q.{w}
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
  let F := Q.objPreimage (R.obj N)
  let eN : R.obj N ≅ Q.obj F := (Q.objObjPreimageIso (R.obj N)).symm
  let hcomp := strictlyPerfect_localHom_computations X U P hstrict
  let f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F :=
    { f := localEvaluationDegreeMap X U P F
      comm' := fun n m h ↦ localEvaluationDegreeMap_comm X U P F n m h }
  let hf : IsLocalOrdinaryEvaluation X U P F f :=
    fun p q n r hpq ↦ localEvaluationDegreeMap_formula X U P F p q n r hpq
  let hcmp := exists_exactSource_evaluation_local_comparisons
    X K N U P F hcomp.1 hcomp.2 eK eN f hf
  let a := hcmp.choose
  let hcmp' := hcmp.choose_spec
  let b := hcmp'.choose
  let hab := hcmp'.choose_spec
  have : ∀ n : ℤ, IsIso (f.f n) :=
    fun n ↦ isIso_localOrdinaryEvaluation_degree X U P F hstrict f hf n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  refine ⟨b.hom ≫ (Q.mapIso (asIso f)).inv ≫ a.inv, ?_⟩
  change R.map g ≫ b.hom = a.hom ≫ (Q.mapIso (asIso f)).hom at hab
  rw [← Category.assoc, ← Category.assoc, hab]
  simp only [Category.assoc, Iso.hom_inv_id, Category.id_comp]


end AlgebraicGeometry
