/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Sheaf.AlgebraicGeometry.ProEtaleSectionsLimitsColimits

/-!
# Exact and cocontinuous sections on weakly contractible affines

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-cor-pe-bounded-continuity/sk-lem-proper-heart-continuity-sections.md
(blueprint: det-proper-heart-continuity-sections).
-/

@[expose] public section

universe u r v wJ uJ

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace CategoryTheory

/--
Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-cor-pe-bounded-continuity/sk-lem-proper-heart-continuity-sections.proof.md
(blueprint: det-proper-heart-continuity-sections).

Apply `peSectionsLimitsColimits` to obtain preservation of all limits and colimits
for evaluation at `W`.  Evaluation is additive and linear on sections by the
sheaf-of-modules category.  Preservation of finite kernels and cokernels therefore
makes the evaluated short exact module sequence short exact after forgetting to
abelian groups.  For an arbitrary diagram, the colimit is the quotient of the
coproduct by the relations from its arrows; the same presentation after forgetting
scalars proves preservation of all colimits in abelian groups, including the empty,
discrete, and filtered cases.
-/
theorem properHeartContinuitySections {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{r})
    (W : X.ProEt) [IsAffine W.left]
    (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{max (u + 1) r v} W) :
    exactFunctor (SheafOfModules.{max (u + 1) r v} R) (AddCommGrpCat.{max (u + 1) r v})
        (SheafOfModules.evaluation R (op W) ⋙ forget₂ _
          AddCommGrpCat.{max (u + 1) r v}) ∧
      PreservesColimitsOfSize.{wJ, uJ}
        (SheafOfModules.evaluation R (op W) ⋙ forget₂ _
          AddCommGrpCat.{max (u + 1) r v}) := by
  have hE := peSectionsLimitsColimits.{u, r, v, 0, 0} R W hW
  have := hE.1
  have := hE.2
  have hE' := peSectionsLimitsColimits.{u, r, v, wJ, uJ} R W hW
  have := hE'.2
  let U := forget₂ (ModuleCat.{max (u + 1) r v} (R.obj.obj (op W)))
    AddCommGrpCat.{max (u + 1) r v}
  let A := (ModuleCat.restrictCoextendScalarsAdj.{max (u + 1) r v}
    (Int.castRingHom (R.obj.obj (op W)))).comp
    (forget₂ (ModuleCat.{max (u + 1) r v} ℤ)
      AddCommGrpCat.{max (u + 1) r v}).asEquivalence.toAdjunction
  let B := A.ofNatIsoLeft
    (show U ≅ _ from NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))
  have : PreservesColimitsOfSize.{wJ, uJ} U := B.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} U := B.leftAdjoint_preservesColimits
  have : PreservesFiniteLimits U := inferInstance
  have : PreservesFiniteColimits U :=
    PreservesColimitsOfSize.preservesFiniteColimits U
  constructor
  · change exactFunctor _ _ (SheafOfModules.evaluation R (op W) ⋙ U)
    exact (exactFunctor_iff _).2
      ⟨comp_preservesFiniteLimits _ U, comp_preservesFiniteColimits _ U⟩
  · exact comp_preservesColimits (SheafOfModules.evaluation R (op W)) U

end CategoryTheory
