/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 as described in the file LICENSE.
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
import Sheaf.AlgebraicGeometry.LocallyClosedStratification
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.ExtOneExtensionClassification
import Sheaf.Paper.CondensedSheafExtContinuity
import Sheaf.Paper.ProfinitePointPullback

/-! Intermediate support-induction branch. -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option linter.style.haveILetI false

/- The two interfaces below isolate the geometric localization and algebraic
  extension-class descent parts of the support induction argument. -/

/-- Glue compatible open/closed models by finite-stage extension classification.

Source: `ModuleObject/Colimit/TwoColimit.lean`, support-induction split; tensor
adjunction, Ext-continuity and Serre closure perform the gluing. Proof: Enlarge EU and EZ
to their finite compositum and extend the two models to it. Let N be the pullback of M to
Y. Open/closed localization expresses N as an extension of the closed direct image of its
restriction to Z by the open extension by zero of its restriction to U. Extend the two
finite-field models by these functors. Their finite stratifications combine to prove
constructibility. Scalar extension commutes with open extension by zero by its
tensor-restriction adjunction; it commutes with closed direct image at finite stages by a
finite field basis and at the algebraic closure by filtered-colimit continuity. Thus these
objects model the outer terms of the localization sequence. Exact scalar extension and
exact restriction induce the derived adjunction. Under this adjunction the localization
extension class is a degree-one map into the filtered colimit of finite-stage extensions of
the open model. Ext-continuity for the constructible closed model represents it at one
finite stage. The finite-stage adjunction and extension classification produce a short exact
sequence over that field. Serre closure makes its middle term constructible. Exact scalar
extension preserves its extension class, and extension classification identifies the extended
middle term with N.
(blueprint: new-lem-weil-pbc-condensed-stratum-model-induction-step-nonempty-gluing)
-/
theorem glue_nonempty_support_open_closed_models
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ))
    {Y : Scheme.{u}} (i : Y ⟶ T) [IsClosedImmersion i] [Nonempty Y]
    {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    {Z : Scheme.{u}} (k : Z ⟶ Y) [IsClosedImmersion k]
    (hcover : Set.range j ∪ Set.range k = Set.univ)
    (hdisj : Disjoint (Set.range j) (Set.range k))
    (EU : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (PU : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (padicSubfieldRingObj U ℓ EU))
    (EZ : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (PZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (padicSubfieldRingObj Z ℓ EZ))
    (hPU : IsConstructibleModuleObject (padicSubfieldRingObj U ℓ EU) PU)
    (hPZ : IsConstructibleModuleObject (padicSubfieldRingObj Z ℓ EZ) PZ)
    (eU : Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl U ℓ EU)).obj PU ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (j ≫ i)).obj M))
    (eZ : Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Z ℓ EZ)).obj PZ ≅
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (k ≫ i)).obj M)) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (padicSubfieldRingObj Y ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj Y ℓ E) P ∧
      Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y ℓ E)).obj P ≅
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) i).obj M) := by
  sorry


end AlgebraicGeometry.ProEtale
