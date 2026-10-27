/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.FiniteClopenExceptionalRestriction
public import Sheaf.Paper.FiniteClopenDecompositionCore
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import Sheaf.Paper.SmoothClopenResidueLine
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.PurityFiniteSettingComparisonHypotheses
import Mathlib.Data.Nat.Prime.Infinite

/-! # Pure-dimensional component inverses for the recorded exceptional systems

Source: blueprint smooth cohomological smoothness, first paragraph, and
section-invariant, Step 4 of finite-clopen inverse assembly.
(blueprint: lem-pur-smooth-clopen-component-inverse).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem complete_of_constructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) (M : sfIntegralConstructibleCategory l E W) :
    IntegralOnSlice.IsComplete l E W none M.obj := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E W D hl M.obj).mp M.property.1⟩

private noncomputable def integral_tensor_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) :
    integralCompletedTensor l E W ≅ IntegralOnSlice.completedTensor l E W none := by
  let e := Classical.choice (IntegralOnSlice.completedTensor_global_comparison l E W)
  exact ((integralCompletedTensorDescent l E W).universal _ e).exists.choose


variable (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

private theorem integral_component_inverse
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    [∀ x : Xi.left, Invertible (P.coefficients.l : Xi.left.residueField x)]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (R : ClopenExceptionalCoefficientComparison P E X Y Xi g c j)
    (d : ℕ) [SmoothOfRelativeDimension d (j.left ≫ g)] :
    let U : sfIntegralConstructibleCategory P.coefficients.l E Y.left :=
      ⟨integralConstantCoefficientObject P.coefficients.l E Y.left,
        (integralConstantCoefficient_constructible P.coefficients.l E Y.left
          P.field P.coefficients.different).2.1⟩
    let omega := R.integralI.obj U
    finiteTorConstructibleIntegral P.coefficients.l E Xi.left omega.obj ∧
      ∃ Q, finiteTorConstructibleIntegral P.coefficients.l E Xi.left Q.obj ∧
        Nonempty ((constructibleIntegralTensor P.coefficients.l E Xi.left).obj (omega, Q) ≅
          ⟨integralConstantCoefficientObject P.coefficients.l E Xi.left,
            (integralConstantCoefficient_constructible P.coefficients.l E Xi.left
              P.field P.coefficients.different).2.1⟩) ∧
        Nonempty ((constructibleIntegralTensor P.coefficients.l E Xi.left).obj (Q, omega) ≅
          ⟨integralConstantCoefficientObject P.coefficients.l E Xi.left,
            (integralConstantCoefficient_constructible P.coefficients.l E Xi.left
              P.field P.coefficients.different).2.1⟩) := by
  let U : sfIntegralConstructibleCategory P.coefficients.l E Y.left :=
    ⟨integralConstantCoefficientObject P.coefficients.l E Y.left,
      (integralConstantCoefficient_constructible P.coefficients.l E Y.left
        P.field P.coefficients.different).2.1⟩
  let omega := R.integralI.obj U
  obtain ⟨L, hL, hres⟩ := smooth_clopen_residue_line P E X Y g Xi c j R d
  have : IsNoetherian Xi.left :=
    (finite_setting_comparison_hypotheses P
      (Xi.left ↘ Spec (.of P.field.k)) (Y.left ↘ Spec (.of P.field.k)) (j.left ≫ g)
      ((Scheme.Hom.isOver_iff (Spec (.of P.field.k))).mp inferInstance)).1
  obtain ⟨T, _hT, _hmodel, _hreductions, hM, hQ, _hev, _hev', _hbounds,
      _hcomplete, _hcomplete', _hcomp, _hcomp', e, e', _he, _he'⟩ :=
    completeResidueLineInverse P.coefficients.l E Xi.left
      (P.coefficientPrime_isUnit_stalk Xi.left Xi.hom) omega.obj
      (complete_of_constructible P.coefficients.l E Xi.left omega) (2 * (d : ℤ)) L hL hres
  let Q : sfIntegralConstructibleCategory P.coefficients.l E Xi.left :=
    ⟨completeResidueDual P.coefficients.l E Xi.left omega.obj, hQ.1⟩
  let a := integral_tensor_comparison P.coefficients.l E Xi.left
  refine ⟨hM, Q, hQ, ?_, ?_⟩
  · exact ⟨(sfIntegralConstructible P.coefficients.l E Xi.left).fullyFaithfulι.preimageIso
      (a.app (omega.obj, Q.obj) ≪≫ e)⟩
  · exact ⟨(sfIntegralConstructible P.coefficients.l E Xi.left).fullyFaithfulι.preimageIso
      (a.app (Q.obj, omega.obj) ≪≫ e')⟩

private noncomputable def rational_tensor_localization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (rationalDerivedTensor l E W).obj
        ((sfRationalConstructibleLocalization l E W).obj M,
          (sfRationalConstructibleLocalization l E W).obj N) ≅
      (sfRationalConstructibleLocalization l E W).obj
        ((constructibleIntegralTensor l E W).obj (M, N)) :=
  eqToIso ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 _)

private theorem rational_component_inverse
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    [∀ x : Xi.left, Invertible (P.coefficients.l : Xi.left.residueField x)]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (R : ClopenExceptionalCoefficientComparison P E X Y Xi g c j)
    (d : ℕ) [SmoothOfRelativeDimension d (j.left ≫ g)] :
    let U : sfIntegralConstructibleCategory P.coefficients.l E Y.left :=
      ⟨integralConstantCoefficientObject P.coefficients.l E Y.left,
        (integralConstantCoefficient_constructible P.coefficients.l E Y.left
          P.field P.coefficients.different).2.1⟩
    let V : sfIntegralConstructibleCategory P.coefficients.l E Xi.left :=
      ⟨integralConstantCoefficientObject P.coefficients.l E Xi.left,
        (integralConstantCoefficient_constructible P.coefficients.l E Xi.left
          P.field P.coefficients.different).2.1⟩
    let omega := R.rationalI.obj ((sfRationalConstructibleLocalization
      P.coefficients.l E Y.left).obj U)
    ∃ Q, Nonempty ((rationalDerivedTensor P.coefficients.l E Xi.left).obj (omega, Q) ≅
        (sfRationalConstructibleLocalization P.coefficients.l E Xi.left).obj V) ∧
      Nonempty ((rationalDerivedTensor P.coefficients.l E Xi.left).obj (Q, omega) ≅
        (sfRationalConstructibleLocalization P.coefficients.l E Xi.left).obj V) := by
  obtain ⟨_hM, Q, _hQ, ⟨e⟩, ⟨e'⟩⟩ := integral_component_inverse P X Y g E Xi c j R d
  dsimp only
  rw [R.coherence.2.2.2.2.1]
  let loc := sfRationalConstructibleLocalization P.coefficients.l E Xi.left
  refine ⟨loc.obj Q, ?_, ?_⟩
  · exact ⟨rational_tensor_localization P.coefficients.l E Xi.left _ Q ≪≫ loc.mapIso e⟩
  · exact ⟨rational_tensor_localization P.coefficients.l E Xi.left Q _ ≪≫ loc.mapIso e'⟩

private noncomputable def common_stage_tensor_at_stage
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    [∀ x : W, Invertible (l : W.residueField x)]
    (A : AlgebraicallyClosedCoefficients.Index l Ω)
    (K L : GeneralAlgebraicallyClosedCoefficients.Stage l Ω W A) :
    (commonStageDerivedTensor l Ω W).obj (⟨A, K⟩, ⟨A, L⟩) ≅
      ⟨A, (rationalDerivedTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) W).obj (K, L)⟩ := by
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω W
  let h : (commonStageTensorObject l Ω W ⟨A, K⟩ ⟨A, L⟩).stage ≤ A :=
    show A.val ⊔ A.val ≤ A.val from sup_le le_rfl le_rfl
  let unit : S.T (le_rfl : A ≤ A) ≅ 𝟭 _ :=
    operationStageTransitionIso l Ω W A A le_rfl ≪≫
      GeneralAlgebraicallyClosedCoefficients.unitor l Ω W A
  exact eqToIso ((commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1 _ _) ≪≫
    S.isoToStage _ h ≪≫
    (S.ι A).mapIso (commonStageTensorComparison l Ω W ⟨A, K⟩ ⟨A, L⟩ A h ≪≫
      (rationalDerivedTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) W).mapIso
          (Iso.prod (unit.app K) (unit.app L)))

/-- A pure-dimensional smooth component has an inverse at integral and field
coefficients, for the actual component functors of any normalized comparison.
There is no gluing, common global system, or assertion about prescribed maps here.

Source: blueprint thm-pur-cohomological-smoothness, first paragraph; Step 4 of
lem-pur-varying-dimension-dualizing-inverse, integral and field coefficient clauses.
(blueprint: lem-pur-smooth-clopen-component-inverse).

Proof: Xi is Noetherian and the coefficient prime is invertible on its stalks,
because Xi is finite type over the fixed field. Compare R.base.integralI with the
normalized integral exceptional functor for c.precomp j.left by the unique
counit-preserving comparison of right adjoints: both are right adjoint to the
same specified integral compact-support functor. Its value on the unit is
therefore isomorphic to the normalized integral dualizing object. Use that
object's actual strict reduction system and canonical derived-limit realization,
not an arbitrary tower with the same limit. Its finite reductions are the finite
exceptional images of the reduced unit. At residue level smooth tensor duality
in pure relative dimension d identifies this image with the intrinsic comparison
image of an etale line shifted by 2d; the finite exceptional adjunction comparison
fixes that identification. Carry it back through the reduction of the integral
right-adjoint comparison. The construction works without a trivialization of the line.
Apply completeResidueLineInverse to this complete integral object with m = 2d.
It supplies its internal-Hom dual, both completed-tensor evaluation isomorphisms,
and uniform Tor intervals [-2d,-2d] and [2d,2d]. The original object and its dual
are constructible and complete, so the evaluations lift through the fully faithful
integral constructible inclusion. The tensor and unit are exactly the completed
operations used by clopenIntegralTensor and clopenIntegralUnit. This proves the
first assertion, including the finite-Tor membership of both objects.
Apply the rational localization functor to the same pair. Its tensor comparison
is defined on these integral representatives and preserves both evaluations.
The rationalObjectI coherence field identifies its first factor with the actual
rationalI image of the unit, giving the second assertion. Repeat the argument at
the finite coefficient field indexed by A, using R.stage A. The stage_eqI field
identifies its rational exceptional functor with R.actionI at A. Represent the
inverse and evaluations at that same stage and use the normalized tensor and
unit comparisons of common-stage operations; identity scalar extension is
included. This proves the third assertion for every A. All statements allow the
empty component: its categories are zero and the displayed maps are unique. -/
theorem smooth_clopen_component_inverse
    (Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (R : ClopenExceptionalAllCoefficients P X Y Xi g c j)
    (d : ℕ) [SmoothOfRelativeDimension d (j.left ≫ g)] :
    (let omega := R.base.integralI.obj (P.clopenIntegralUnit Y.left)
     finiteTorConstructibleIntegral P.coefficients.l P.extension Xi.left omega.obj ∧
       ∃ Q, finiteTorConstructibleIntegral P.coefficients.l P.extension Xi.left Q.obj ∧
         Nonempty ((P.clopenIntegralTensor Xi).obj (omega, Q) ≅
           P.clopenIntegralUnit Xi.left) ∧
         Nonempty ((P.clopenIntegralTensor Xi).obj (Q, omega) ≅
           P.clopenIntegralUnit Xi.left)) ∧
    (let omega := R.base.rationalI.obj (P.clopenRationalUnit Y.left)
     ∃ Q, Nonempty ((P.clopenRationalTensor Xi).obj (omega, Q) ≅
         P.clopenRationalUnit Xi.left) ∧
       Nonempty ((P.clopenRationalTensor Xi).obj (Q, omega) ≅
         P.clopenRationalUnit Xi.left)) ∧
    (∀ A : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar,
     let omega := R.actionI.functor.obj (P.clopenCommonStageUnit Y.left A)
     ∃ Q, Nonempty ((P.clopenCommonStageTensor Xi).obj (omega, Q) ≅
         P.clopenCommonStageUnit Xi.left A) ∧
       Nonempty ((P.clopenCommonStageTensor Xi).obj (Q, omega) ≅
         P.clopenCommonStageUnit Xi.left A)) := by
  let : ∀ x : Xi.left, Invertible (P.coefficients.l : Xi.left.residueField x) :=
    fun x ↦ (P.clopenResidue_isUnit Xi x).invertible
  refine ⟨?_, ?_, ?_⟩
  · exact integral_component_inverse P X Y g P.extension Xi c j R.base d
  · exact rational_component_inverse P X Y g P.extension Xi c j R.base d
  · intro A
    obtain ⟨Q, ⟨e⟩, ⟨e'⟩⟩ := rational_component_inverse P X Y g
      (AlgebraicallyClosedCoefficients.Coefficient.{u}
        P.coefficients.l P.coefficients.Qbar A) Xi c j (R.stage A) d
    change ∃ Q, Nonempty ((P.clopenCommonStageTensor Xi).obj
        (⟨A, (R.actionI.Φ A).obj _⟩, Q) ≅ P.clopenCommonStageUnit Xi.left A) ∧
      Nonempty ((P.clopenCommonStageTensor Xi).obj
        (Q, ⟨A, (R.actionI.Φ A).obj _⟩) ≅ P.clopenCommonStageUnit Xi.left A)
    rw [R.coherence.2.1 A]
    let inc := (GeneralAlgebraicallyClosedCoefficients.stageSystem
      P.coefficients.l P.coefficients.Qbar Xi.left).ι A
    refine ⟨⟨A, Q⟩, ?_, ?_⟩
    · exact ⟨common_stage_tensor_at_stage P.coefficients.l P.coefficients.Qbar Xi.left A _ Q ≪≫
        inc.mapIso e⟩
    · exact ⟨common_stage_tensor_at_stage P.coefficients.l P.coefficients.Qbar Xi.left A Q _ ≪≫
        inc.mapIso e'⟩

end WeilConjectures.PurityFiniteSetting
