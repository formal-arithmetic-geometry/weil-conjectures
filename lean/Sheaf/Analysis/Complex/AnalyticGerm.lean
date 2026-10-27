module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Filter.Germ.Basic

/-! # Analytic germs at the origin

Source: Frenkel, Séminaire H. Cartan 1951–52, exposé 10, §4, pp. 6–7
(blueprint: def-sfb-complex-analytic-germ).
-/

@[expose] public section

set_option autoImplicit false

open Topology

namespace Complex.Taylor

/-- The germs at zero having a convergent power-series representative. `Filter.Germ`
identifies precisely functions agreeing on a neighbourhood of zero. No global analyticity
of the representative is imposed.
Source: Frenkel, exposé 10, §4 (blueprint: def-sfb-complex-analytic-germ). -/
def AnalyticGerm (d : ℕ) :=
  {g : Filter.Germ (𝓝 (0 : Fin d → ℂ)) ℂ //
    ∃ f : (Fin d → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧ Filter.Germ.ofFun f = g}

end Complex.Taylor
