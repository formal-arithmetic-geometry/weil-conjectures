/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
public import Mathlib.Algebra.Category.ModuleCat.Basic

import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars

/-!
# Compatible evaluation functors for two lifts of a scheme point

## References

* Hemo--Richarz--Scholbach, Example 3.1
* Bhatt--Scholze, Example 4.2.11
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Compatible geometric evaluation, independent of any chosen module or presentation
(Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Example 4.2.11). -/
theorem exists_condensedField_compatible_evaluations
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    (X V W : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (p : V ⟶ X) (g : W ⟶ X)
    (a : Spec (.of Ω) ⟶ V) (d : Spec (.of Ω) ⟶ W)
    (had : a ≫ p = d ≫ g) (z : Spec (.of Ω)) :
    let R := condensedRingObj (condensedFieldCoefficientRingObj E) X
    let Ri := (upperStar AddCommGrpCat.{u + 1} p).obj R
    let Rj := (upperStar AddCommGrpCat.{u + 1} g).obj R
    ∃ (F : Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) Ri ⥤
        ModuleCat.{u + 1} E)
      (G : Mod (Sheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}) Rj ⥤
        ModuleCat.{u + 1} E),
      F.Additive ∧ G.Additive ∧ PreservesFiniteColimits F ∧ PreservesFiniteColimits G ∧
      Nonempty (((upperStar AddCommGrpCat.{u + 1} p).mapMod R) ⋙ F ≅
        ((upperStar AddCommGrpCat.{u + 1} g).mapMod R) ⋙ G) ∧
      ∃ (b : F.obj (Mod.regular Ri) ≃ₗ[E] E)
        (c : G.obj (Mod.regular Rj) ≃ₗ[E] E),
        (∀ f : Mod.regular Ri ⟶ Mod.regular Ri,
          b (F.map f (b.symm 1)) =
            condensedFieldContinuousCoefficientMap E V
              (inv (condensedFieldPullbackRealization E p) ≫ f.hom ≫
                condensedFieldPullbackRealization E p) (a z)) ∧
        (∀ f : Mod.regular Rj ⟶ Mod.regular Rj,
          c (G.map f (c.symm 1)) =
            condensedFieldContinuousCoefficientMap E W
              (inv (condensedFieldPullbackRealization E g) ≫ f.hom ≫
                condensedFieldPullbackRealization E g) (d z)) := by
  let Λ := condensedFieldCoefficientRingObj E
  let R := condensedRingObj Λ X
  obtain ⟨H, hHa, hHc, hHs⟩ := exists_condensedField_point_evaluation E Ω z
  let := hHa
  let := hHc
  let P := condensedFieldGeometricModulePullback (condensedFieldCoefficientRingObj E) p a
  let Q := condensedFieldGeometricModulePullback (condensedFieldCoefficientRingObj E) g d
  let F := P ⋙ H
  let G := Q ⋙ H
  let e : (upperStar AddCommGrpCat.{u + 1} p).mapMod R ⋙ F ≅
      (upperStar AddCommGrpCat.{u + 1} g).mapMod R ⋙ G :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (condensedFieldGeometricModulePullbackComp Λ p a) H ≪≫
      Functor.isoWhiskerRight (eqToIso (congrArg (CondensedRing.upperStar Λ) had)) H ≪≫
      (Functor.isoWhiskerRight (condensedFieldGeometricModulePullbackComp Λ g d) H).symm ≪≫
      Functor.associator _ _ _
  obtain ⟨b, hb⟩ := condensedField_geometric_evaluation_scalars E X V Ω p a z H hHs
  obtain ⟨c, hc⟩ := condensedField_geometric_evaluation_scalars E X W Ω g d z H hHs
  refine ⟨F, G, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨e⟩, b, c, ?_, ?_⟩
  · exact hb
  · exact hc

end AlgebraicGeometry.ProEtale
