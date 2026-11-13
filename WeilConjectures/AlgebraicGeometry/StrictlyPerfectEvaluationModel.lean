/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons

/-! # The local ordinary model of canonical derived evaluation

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Conversion between the localized carrier and the Hom carrier needs extra elaboration steps.
/-- The restricted canonical adjunct is the localization of ordinary evaluation,
with the source and target comparison isomorphisms included in the commuting square.
This assertion does not say that the evaluation chain map is invertible.
-/
theorem strictlyPerfect_evaluation_local_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ F : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
      Nonempty (R.obj N ≅ DerivedCategory.Q.obj F) ∧
      ∃ f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F,
        IsLocalOrdinaryEvaluation X U P F f ∧
        ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
          ∃ b : R.obj (H.obj (op K, N)) ≅
              DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
            R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f := by
  classical
  let R := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory
  let Q := DerivedCategory.Q.{w}
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
  let F := Q.objPreimage (R.obj N)
  let eN : R.obj N ≅ Q.obj F := (Q.objObjPreimageIso (R.obj N)).symm
  let f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F :=
    { f := localEvaluationDegreeMap X U P F
      comm' := fun n m h ↦ localEvaluationDegreeMap_comm X U P F n m h }
  have hf : IsLocalOrdinaryEvaluation X U P F f := by
    intro p q n r h
    exact localEvaluationDegreeMap_formula X U P F p q n r h
  obtain ⟨eK⟩ := hP
  obtain ⟨a, b, hab⟩ := exists_strictlyPerfect_evaluation_comparisons
    X K N U P F hstrict eK eN f hf
  exact ⟨F, ⟨eN⟩, f, hf, a, b, hab⟩

end AlgebraicGeometry
