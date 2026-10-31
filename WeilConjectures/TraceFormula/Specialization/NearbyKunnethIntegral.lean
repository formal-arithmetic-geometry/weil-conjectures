/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFormula
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethProper
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Gabber's Künneth formula with integral coefficients: the induction

WIP skeleton: the integral induction of PR #1795 (see the PR description). The statements
`sliceKunnethFormula_padicIntegers`, `sliceKunnethFormula_padicAlgCl` and
`isIso_kunnethMap_padicIntegers_of_isProper` are being proved in sibling files.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Gabber's Künneth formula with `𝒪_E`-coefficients in chart dimension `n`**, for every finite
subextension `E ⊆ ℚ̄_ℓ` (`NearbyCyclesModel.KunnethFormula` for `Λ = 𝒪_E`). -/
def IntegralKunnethFormula (k' : Type u) [Field k'] (n : ℕ) : Prop :=
  ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
    KunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' n

variable {ℓ} {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

/-- WIP: the `𝒪_E` generic-slicing step from the integral Künneth formula over `Spec K⟦t⟧`. -/
theorem sliceKunnethFormula_padicIntegers {n : ℕ}
    (hIH : IntegralKunnethFormula ℓ (traitSliceField k') n)
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    SliceKunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' n :=
  sorry

/-- WIP: the `ℚ̄_ℓ` generic-slicing step from the `𝒪_E` ones (integral models). -/
theorem sliceKunnethFormula_padicAlgCl {n : ℕ}
    (h : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SliceKunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' n) :
    SliceKunnethFormula (Profinite.padicAlgClRingObj ℓ) k' n :=
  sorry

variable {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {N : NearbyCyclesModel Y Y'.left}
  {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X} {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y}
  {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'} {φ₂ : P.Hom N f₂ f₂'}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {qN : N.total ⟶ trait k'} {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- WIP: the integral Künneth formula for proper models, given the generic-slicing steps. -/
theorem isIso_kunnethMap_padicIntegers_of_isProper (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) [IsProper qM] [IsProper qN]
    {m m' : ℕ} (hm : qM.LocallyEmbedsInAffineSpace m) (hm' : qN.LocallyEmbedsInAffineSpace m')
    (hslice : 0 < m + m' → ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SliceKunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' (m + m' - 1))
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y) B) :
    IsIso (kunnethMap (Profinite.padicIntegersRingObj ℓ E.1) φ₁ φ₂ A B) :=
  sorry

variable (ℓ) in
omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- **Gabber's Künneth formula with `𝒪_E`-coefficients in every chart dimension**, by induction
on the chart dimension `n`, simultaneously for all separably closed fields `k'`
(`NearbyCyclesModel.IntegralKunnethFormula`). By the reduction to proper models
(`NearbyCyclesModel.isIso_kunnethMap_of_properKunnethFormula`), this is
`NearbyCyclesModel.isIso_kunnethMap_padicIntegers_of_isProper`, whose generic-slicing inputs
come from the induction hypothesis over the trait `Spec K⟦t⟧`, `K = k'(x)^alg`
(`NearbyCyclesModel.sliceKunnethFormula_padicIntegers`). -/
theorem integralKunnethFormula (n : ℕ) :
    ∀ (k' : Type u) [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
      [Fact (ringChar k' ≠ ℓ)], IntegralKunnethFormula ℓ k' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k' _ _ _ _ E X Y Z X' Y' Z' M N P f₁ f₁' f₂ f₂' φ₁ φ₂ qM gM qN gN hM hN hpb hP hgen m₁ m₂
    hle h₁ h₂ eM heM eN heN A B hA hB
  refine isIso_kunnethMap_of_properKunnethFormula (n := n)
    (fun {X Y Z X' Y' Z' M N P f₁ f₁' f₂ f₂'} φ₁ φ₂ {qM gM qN gN} hM hN hpb hP hgen hqM hqN
      {m₁ m₂} hle h₁ h₂ {eM} heM {eN} heN {A B} hA hB ↦ ?_) hM hN hpb hP hgen hle h₁ h₂ heM heN
    hA hB
  have hslice : 0 < m₁ + m₂ → ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SliceKunnethFormula (Profinite.padicIntegersRingObj ℓ E.1) k' (m₁ + m₂ - 1) :=
    fun hpos E ↦ by
      have : Fact (ringChar (traitSliceField k')).Prime :=
        ⟨by rw [ringChar_traitSliceField]; exact Fact.out⟩
      have : Fact (ringChar (traitSliceField k') ≠ ℓ) :=
        ⟨by rw [ringChar_traitSliceField]; exact Fact.out⟩
      have hIH : IntegralKunnethFormula ℓ (traitSliceField k') (m₁ + m₂ - 1) :=
        @ih (m₁ + m₂ - 1) (by omega) (traitSliceField k') _ _ _ _
      have h := sliceKunnethFormula_padicIntegers (k' := k') hIH E
      exact h
  have := hqM
  have := hqN
  exact isIso_kunnethMap_padicIntegers_of_isProper hM hN hpb hP hgen h₁ h₂ hslice heM heN E hA hB

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

/-- WIP: the `ℚ̄_ℓ` Künneth formula from the `𝒪_E` ones (integral models and coefficient
change). -/
theorem kunnethFormula_padicAlgCl_of_integral {n : ℕ} (h : IntegralKunnethFormula ℓ k' n) :
    KunnethFormula (Profinite.padicAlgClRingObj ℓ) k' n :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
