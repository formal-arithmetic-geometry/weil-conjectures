module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Hartogs extension across the origin

Source: Demailly, Complex Analytic and Differential Geometry, I §3.D,
Theorem (3.28), printed p.28, specialized to the origin in complex affine space.
(blueprint: lem-sfb-hartogs-punctured-affine-extension)

The input is a total function whose value at the origin is ignored. Analyticity
and agreement are required only on the complement of the origin, so this presents
exactly a holomorphic function on the punctured space.
-/

@[expose] public section

set_option autoImplicit false

namespace Complex

/-- Every holomorphic function on punctured complex affine space of dimension at
least two has a unique entire extension, without a growth or continuity condition
at the origin.

Source: Demailly, Complex Analytic and Differential Geometry, I §3.D,
Theorem (3.28), printed p.28.
(blueprint: lem-sfb-hartogs-punctured-affine-extension)

Proof plan:
1. Write the coordinates as `(z,w)` with `w` in `m-1` coordinates. Integrate
   `f(ζ,w)/(ζ-z)` on the positively oriented unit circle and divide by `2πi`.
   The parameter-integral lemma gives a holomorphic function `H` on the product
   of the unit disc with the unit polydisc, since the integration annulus avoids
   the origin (lem-sfb-holomorphic-circle-integral-parameters).
2. For nonzero `w`, the slice `z ↦ f(z,w)` is entire by analytic composition
   (lem-sfb-complex-analytic-function-operations). Its analytic germs are
   differentiable (lem-sfb-analytic-germ-differentiable). The one-variable
   Cauchy formula gives `H(z,w)=f(z,w)` (lem-sfb-cauchy-circle-formula).
3. For nonzero `z`, approach `w=0` through nonzero vectors in the polydisc.
   Such vectors exist because `m-1 ≥ 1`. Continuity of the analytic functions
   gives `H(z,0)=f(z,0)`. Thus `H=f` on the punctured polydisc.
4. Set `F(0)=H(0,0)` and `F(x)=f(x)` for nonzero `x`. Near the origin this
   equals `H`, and near every other point it equals `f`, so `F` is entire.
5. Two entire extensions agree off zero. Their continuity along the sequence
   `(1/(k+2),0,...,0)` tending to zero forces equality at zero as well.
   No boundedness or prescribed limit of the input was used. -/
theorem existsUnique_entire_extension_of_punctured_affine
    (m : ℕ) (hm : 2 ≤ m) (f : (Fin m → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f ({0}ᶜ : Set (Fin m → ℂ))) :
    ∃! F : (Fin m → ℂ) → ℂ,
      AnalyticOnNhd ℂ F Set.univ ∧ Set.EqOn F f ({0}ᶜ : Set (Fin m → ℂ)) := by
  sorry

end Complex
