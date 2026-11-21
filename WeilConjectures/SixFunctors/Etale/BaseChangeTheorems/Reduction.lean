/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma.ProjectiveDomination
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Cancellation
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# The reduction of proper base change to the projective line

Assume that the projection `ℙ¹_S ⟶ S` satisfies the base change property
`AlgebraicGeometry.Etale.HasTorsionBaseChange` for every scheme `S`. Then every proper morphism
satisfies it (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper`).

## References

- Stacks Project, Lemma 59.91.10, <https://stacks.math.columbia.edu/tag/0A4F>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale ProjectiveSpace

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A finite morphism satisfies the base change property for every coefficient ring. -/
theorem Etale.hasTorsionBaseChange_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_isBaseChangeIso Λ f

/-- The tower `(ℙ¹_S)ⁿ ⟶ S` satisfies the base change property if all projective lines do, the
coefficient ring being torsion. -/
theorem Etale.hasTorsionBaseChange_projectiveLinePowProj (hΛ : IsAddTorsion Λ)
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S)) (n : ℕ)
    (S : Scheme.{u}) : Etale.HasTorsionBaseChange Λ (projectiveLinePowProj n S) := by
  induction n with
  | zero => exact Etale.hasTorsionBaseChange_of_isFinite Λ (𝟙 S)
  | succ n ih => exact Etale.HasTorsionBaseChange.comp Λ hΛ (h _) ih

/-- **Reduction of projective space to products of lines.** For a torsion coefficient ring `Λ`,
if `ℙ¹_S ⟶ S` satisfies the base change property for every scheme `S`, then so does `ℙⁿ_S ⟶ S`
for every finite index type `n`. -/
theorem Etale.hasTorsionBaseChange_projectiveSpace (hΛ : IsAddTorsion Λ)
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S)) (n : Type u)
    [Finite n] (S : Scheme.{u}) : Etale.HasTorsionBaseChange Λ (ℙ(n; S) ↘ S) := by
  cases isEmpty_or_nonempty n with
  | inl _ => exact Etale.hasTorsionBaseChange_of_isFinite Λ _
  | inr _ =>
    obtain ⟨k, σ, _, _, hσ⟩ := exists_isFinite_surjective_projectiveLinePow n S
    refine Etale.HasTorsionBaseChange.of_comp Λ hΛ (f := σ)
      (Etale.hasTorsionBaseChange_of_isFinite Λ σ) ?_
    rw [hσ]
    exact Etale.hasTorsionBaseChange_projectiveLinePowProj Λ hΛ h k S

/-- **Reduction of proper base change to the projective line, torsion coefficients.** For a
coefficient ring `Λ` which is torsion as an additive group, if `ℙ¹_S ⟶ S` satisfies the base
change property for every scheme `S`, then so does every proper morphism `f : X ⟶ Y`. -/
theorem Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper_of_isAddTorsion
    (hΛ : IsAddTorsion Λ)
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : Etale.HasTorsionBaseChange Λ f := by
  refine Etale.hasTorsionBaseChange_of_affineOpens Λ f fun U ↦ ?_
  have : IsAffine (U : Y.Opens) := U.2
  obtain ⟨D⟩ := ProjectiveDomination.nonempty_of_isAffine (f := f ∣_ (U : Y.Opens))
  have hp := Etale.hasTorsionBaseChange_projectiveSpace Λ hΛ h D.n
  have hπ : Etale.HasTorsionBaseChange Λ D.π := by
    have hw : D.π ≫ f ∣_ (U : Y.Opens) = D.i ≫ ℙ(D.n; _) ↘ _ := D.w.symm
    rw [← ProjectiveSpace.liftBaseChange_over D.π D.i hw]
    exact Etale.HasTorsionBaseChange.comp Λ hΛ (Etale.hasTorsionBaseChange_of_isFinite Λ _)
      (hp _)
  refine Etale.HasTorsionBaseChange.of_comp Λ hΛ hπ ?_
  rw [← D.w]
  exact Etale.HasTorsionBaseChange.comp Λ hΛ (Etale.hasTorsionBaseChange_of_isFinite Λ _) (hp _)

/-- **Reduction of proper base change to the projective line**: if the projection
`ℙ¹_S ⟶ S` satisfies `AlgebraicGeometry.Etale.HasTorsionBaseChange` for every scheme `S`,
then so does every proper morphism of schemes. -/
@[stacks 0A4F]
theorem Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_forall_prime Λ f fun p hp ↦
    Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper_of_isAddTorsion _
      (isAddTorsion_quotient_span_natCast Λ hp.pos) (fun S ↦ (h S).quotient Λ p) f

end AlgebraicGeometry
