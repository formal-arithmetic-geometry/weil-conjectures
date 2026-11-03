/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ZeroSectionCoefficientSupport

/-! # Flat scalar comparison of the actual supported objects

Source: the native-coefficient refinement of Step 3 in the current blueprint
`part-duality-trace-formula/sec-smooth-purity/sec-the-trace-map-of-affine-space/
sk-prop-an/thm-pur-localized-top-chern.proof.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.PurityFiniteSetting

/-- Exact scalar comparison transfers the integral support bound.
Source: the localization-fiber scalar comparison and finite-free scalar extension,
Steps 7--8 of `lem-pur-zero-section-bottom-coefficients`.
Proof: the map at the integral coefficient is the identity. An extension of
integral coefficient rings is finite free, rationalization is localization by
ell, and the closure is the filtered colimit of finite free field extensions.
The corresponding pulled-back module presentations make all the indicated
scalar extensions exact. Use the independent scalar-six ordinary direct-image
comparison on the open complement j, applied to the bounded constructible,
finite-Tor rank-r signed line shifted by 2r. The algebraic closure of a finite
field has ell-cohomological dimension zero, so its finiteness hypothesis holds.
Its compatibility with the adjunction unit identifies the scalar image of the
arrow C -> Rj_*j*C with the corresponding target-coefficient arrow. Exact scalar
extension preserves its fiber; inverse image to the closed subscheme commutes
with scalar extension as well. The root-normalized scalar comparison identifies
the input with the prescribed target signed line. The resulting fiber comparison
is the stated isomorphism between the actual supported objects. The argument
uses no purity isomorphism, trace, or chosen supported generator.
(blueprint: lem-pur-zero-native-flat-scalar-comparison). -/
theorem nativeZeroSupport_scalar_bound
    {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r) :
    ∀ c : PurityTransport.Coefficient P.coefficients.l,
      (match c with | .finite _ _ _ _ => False | _ => True) →
      ∃ hflat : PreservesFiniteLimits
          (Mod.extendScalars (coefficientMap (c.integralMap P.coefficients.l) B)),
        letI := hflat
        Nonempty
          (((Mod.extendScalars
            (coefficientMap (c.integralMap P.coefficients.l) B)).mapDerivedCategory.obj
            (nativeZeroSupport V .integers)) ≅ nativeZeroSupport V c) := by
  sorry

end WeilConjectures.PurityFiniteSetting
