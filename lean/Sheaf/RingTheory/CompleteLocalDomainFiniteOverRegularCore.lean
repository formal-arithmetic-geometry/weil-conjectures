module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.RingTheory.CohenRing
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

universe u
set_option autoImplicit false

namespace IsLocalRing

/--
The coefficient and parameter construction in Stacks Tag 032D produces a regular local
complete subring finite over the given complete local domain. This is the core intermediate
assertion used by the target theorem.
(blueprint: split-complete-local-domain-finite-over-regular-core)
-/
theorem complete_local_domain_finite_over_regular_core
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    ∃ (R₀ : Subring R), ∃ hreg : IsRegularLocalRing R₀,
      let _ := hreg.toIsLocalRing
      IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀ ∧ Module.Finite R₀ R := by
  sorry

end IsLocalRing
