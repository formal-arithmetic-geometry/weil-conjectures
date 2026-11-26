/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
import WeilConjectures.RingTheory.FactorsThroughLocalization

/-!
# Maps from finitely presented algebras factor through smooth algebras

A map from a finitely presented `R`-algebra to an essentially smooth `R`-algebra factors through
a smooth `R`-algebra.

## Implementation details

Writing the essentially smooth algebra as a localization `S⁻¹P` of a smooth `R`-algebra `P`, the
map factors through a principal localization `P[1/s]`
(`factors_through_principal_localization`), which is smooth over `R`.

## References

* [Stacks, Tag 07FJ], proof
-/

@[expose] public section

universe u₁ v₁ w

namespace Algebra

/-- A map from a finitely presented `R`-algebra to an essentially smooth `R`-algebra factors
through a smooth `R`-algebra. -/
theorem essentiallySmooth_factors_through_smooth
    (R : Type u₁) (C : Type v₁) (D : Type w)
    [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [Algebra.FinitePresentation R C]
    (hD : EssentiallySmooth R D) (g : C →ₐ[R] D) :
    ∃ (T : Type (max u₁ v₁ w)) (_ : CommRing T) (_ : Algebra R T),
      Smooth R T ∧ ∃ (f : C →ₐ[R] T) (k : T →ₐ[R] D), k.comp f = g := by
  rcases hD with ⟨P, hP, hRP, hPsmooth, S, ⟨e⟩⟩
  let : CommRing P := hP
  let : Algebra R P := hRP
  obtain ⟨s, f, k, hk⟩ :=
    factors_through_principal_localization R C P S (e.toAlgHom.comp g)
  let : Smooth R P := hPsmooth
  let : Smooth P (Localization.Away (s : P)) := Smooth.of_isLocalization_Away (s : P)
  let : Smooth R (Localization.Away (s : P)) := Smooth.comp R P _
  let T := ULift.{max u₁ v₁ w} (Localization.Away (s : P))
  let a : T ≃ₐ[R] Localization.Away (s : P) := ULift.algEquiv
  refine ⟨T, inferInstance, inferInstance, Smooth.of_equiv a.symm,
    a.symm.toAlgHom.comp f, e.symm.toAlgHom.comp (k.comp a.toAlgHom), ?_⟩
  ext x
  change e.symm (k (f x)) = g x
  have hx : k (f x) = (e : D → Localization S) (g x) := by
    exact DFunLike.congr_fun hk x
  rw [hx]
  exact e.symm_apply_apply (g x)

end Algebra
