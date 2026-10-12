module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Sheaf.AlgebraicGeometry.DivisorModuleLocal
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint

/-!
# Agreement of divisor modules and effective-Cartier line bundles

Source: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/
lem-pc-divisor-line-bundle-agrees-sc (blueprint: lem-pc-divisor-line-bundle-agrees-sc).

## Main statement

For an effective divisor `D = ∑ n_P [P]` (`0 ≤ D`) on a smooth connected curve, the closed
subscheme `D` has ideal sheaf `∏_P I_P ^ n_P`, the product (in the semiring
`Scheme.IdealSheafData`) of powers of the vanishing ideals of the reduced closed points. Its
dual `Scheme.Modules.dual` (the module of def-pc-divisor-line-bundle) is isomorphic to the
divisor module `Divisor.moduleOfSmoothConnectedCurve` (the module of def-sc-divisor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- For an effective divisor `D` on a smooth connected curve, the dual of the ideal sheaf
`∏_P I_P ^ n_P` of `D` (def-pc-divisor-line-bundle) and the divisor module `O_C(D)` of
def-sc-divisor are isomorphic.
Source: blueprint node lem-pc-divisor-line-bundle-agrees-sc
(blueprint: lem-pc-divisor-line-bundle-agrees-sc). -/
theorem divisorLineBundle_agrees_sc (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (D : C.Divisor) (hD : 0 ≤ D) :
    Nonempty (Scheme.Modules.dual (D.prod fun P n ↦
        IdealSheafData.vanishingIdeal ⟨{P.val}, P.prop⟩ ^ n.toNat).toModules ≅
      D.moduleOfSmoothConnectedCurve k C f) := by
  sorry

end AlgebraicGeometry.Scheme
