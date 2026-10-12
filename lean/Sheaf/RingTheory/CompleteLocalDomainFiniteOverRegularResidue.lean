module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.RingTheory.CohenRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

universe u
set_option autoImplicit false

namespace IsLocalRing

/--
After the core subring is chosen, the same construction identifies maximal ideals and residue
fields and supplies the field or Cohen power-series model. This is the remaining intermediate
assertion used by the target theorem.
(blueprint: split-complete-local-domain-finite-over-regular-residue)
-/
theorem complete_local_domain_finite_over_regular_residue
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (R₀ : Subring R) (hreg : IsRegularLocalRing R₀)
    [hlocal : IsLocalRing R₀] (hfinite : Module.Finite R₀ R)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀) :
    IsLocalRing.maximalIdeal R₀ =
        Ideal.comap R₀.subtype (IsLocalRing.maximalIdeal R) ∧
      ∃ e : (R₀ ⧸ IsLocalRing.maximalIdeal R₀) ≃+*
          (R ⧸ IsLocalRing.maximalIdeal R),
        (∀ x : R₀,
          e (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R₀) x) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (R₀.subtype x)) ∧
      ((∃ (k : Type u), ∃ h : Field k, ∃ d : ℕ,
          let _ := h
          Nonempty (R₀ ≃+* MvPowerSeries (Fin d) k)) ∨
      (∃ (Λ : Type u), ∃ h : CommRing Λ, ∃ d : ℕ,
          let _ := h
          ∃ p : ℕ, IsCohenRing p Λ ∧
          Nonempty (R₀ ≃+* MvPowerSeries (Fin d) Λ))) := by
  sorry

end IsLocalRing
