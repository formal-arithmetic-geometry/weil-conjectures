/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectEvaluationModel
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation

/-! # Strictly perfect local tensor--RHom evaluation

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The canonical tensor--RHom evaluation is invertible on an open where its first
argument has a strictly perfect representative. There is no quasi-coherence or
boundedness assumption on the second argument. -/
theorem strictlyPerfect_rhom_evaluation_isIso_on_open
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)) :
    let D := (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf).obj (op K, 𝟙_ (schemeDerivedCategory X))
    IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.map
        (((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
          ((α_ N D K).hom ≫ N ◁
            ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
              (ρ_ N).hom))) := by
  obtain ⟨F, _, f, hf, a, b, h⟩ :=
    strictlyPerfect_evaluation_local_model.{u, w} X K N U P hstrict hP
  have (n : ℤ) : IsIso (f.f n) :=
    isIso_localOrdinaryEvaluation_degree X U P F hstrict f hf n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  have hIso : IsIso (a.hom ≫ DerivedCategory.Q.map f) := inferInstance
  rw [← h] at hIso
  have := hIso
  exact IsIso.of_isIso_comp_right _ b.hom

end AlgebraicGeometry
