/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFamily

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-scalar-counit-equation). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- Change of coefficients for the very same smooth counits. The left arrow is
proper direct-image mate after open extension, and the source arrow is the
normalized scalar/pullback/tensor comparison, also for nonflat finite maps.
Source: coefficient compatibility (blueprint: def-pur-transport-scalar-counit-equation). -/
def ScalarCompatible (D : WeilConjectures.FiniteFieldDatum.{u})
    (b : AdjunctionFamily ell D) : Prop :=
  ∀ (c c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell),
    IsListedScalarCoefficientMap ell a →
    ∃ ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell,
    ∀ s : SmoothDatum D,
    ∃ p : ScalarLineCoordinates ell a ha s.X.left,
    ∀ K : c.ctf ell s.Y.left,
    ∃ hK : property ell c' s.Y.left ((scalarSixChange a s.Y.left).obj K.obj),
      (scalarSixChange a s.Y.left).map ((b c s).trace K) =
        (scalarSupportMap a s.compactification).app
            ((c.smoothSource ell s.map s.dim).obj K.obj) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification).map
              (sourceScalar ell a s.map s.dim ha p K.obj) ≫
          (b c' s).trace ⟨_, hK⟩

end AlgebraicGeometry.ProEtale.PurityTransport
