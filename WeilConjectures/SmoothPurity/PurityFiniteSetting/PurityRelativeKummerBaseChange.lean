/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerRelativeConclusions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerGeometric
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerExchangeFromConclusions

/-! Base change of the normalized affine-line Kummer calculation. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Base-change and geometric-fibre conclusions for a separated finite-type base.
Source: blueprint prop-pur-gm-relative-kummer, Steps 2 and 3.
(blueprint: lem-pur-relative-kummer-base-change-conclusions).
For every map of finite-type bases, obtain the relative conclusions on both bases and
apply the one-map exchange criterion; the geometric-point block uses the same criterion. -/
theorem relative_kummer_base_change_conclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of P.field.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of P.field.k))] :
    (∀ (Y' : Scheme.{u}) [Y'.Over (Spec (CommRingCat.of P.field.k))]
      [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of P.field.k))]
      [QuasiCompact (Y' ↘ Spec (CommRingCat.of P.field.k))]
      [IsSeparated (Y' ↘ Spec (CommRingCat.of P.field.k))]
      (g : Y' ⟶ Y) [g.IsOver (Spec (CommRingCat.of P.field.k))],
      P.KummerBaseChangeConclusions h g (Y ↘ Spec (CommRingCat.of P.field.k))) ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (CommRingCat.of Ω) ⟶ Y),
      P.KummerBaseChangeConclusions h g (Y ↘ Spec (CommRingCat.of P.field.k)) ∧
      P.RelativeKummerConclusions h (Spec (CommRingCat.of Ω))
        (g ≫ Y ↘ Spec (CommRingCat.of P.field.k)) := by
  let a := Y ↘ Spec (CommRingCat.of P.field.k)
  have hY : P.RelativeKummerConclusions h Y a :=
    relative_kummer_relative_conclusions P h Y a
      (fun Ω [Field Ω] [IsAlgClosed Ω] s =>
        relative_kummer_geometric_stalk_conclusions P h Y a Ω s)
  constructor
  · intro Y' _ _ _ _ g _
    have hY' : P.RelativeKummerConclusions h Y' (g ≫ a) :=
      relative_kummer_relative_conclusions P h Y' (g ≫ a)
        (fun Ω [Field Ω] [IsAlgClosed Ω] s =>
          relative_kummer_geometric_stalk_conclusions P h Y' (g ≫ a) Ω s)
    exact relative_kummer_base_change_of_relative_conclusions P h g a hY hY'
  · intro Ω _ _ g
    have hΩ : P.RelativeKummerConclusions h (Spec (CommRingCat.of Ω))
        (g ≫ a) := relative_kummer_geometric_stalk_conclusions P h Y a Ω g
    exact ⟨relative_kummer_base_change_of_relative_conclusions P h g a hY hΩ, hΩ⟩

end WeilConjectures.PurityFiniteSetting
