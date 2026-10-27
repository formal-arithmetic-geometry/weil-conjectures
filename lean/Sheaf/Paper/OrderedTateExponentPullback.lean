/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.FiniteSiteCoordinates

/-! # Pullback of the ordered root transition

Source: finite Tate descent and the canonical Tate identifications in vector integration.
(blueprint: lem-pur-ordered-tate-exponent-pullback)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- Pullback of the ordered shifted Tate coefficient commutes with root transition.
This is a coefficient equation, with no compact support, trace, bundle or frame.
Source: finite Tate site descent, root and pullback normalization; vector integration,
canonical Tate identifications; Stacks 03PK and 03Q1.
(blueprint: lem-pur-ordered-tate-exponent-pullback).

Proof: at degree one the normalized root pullback maps commute with the power map:
both send a root z to the pullback of z raised to ell^(s-r). Cancel the monomorphism
of the roots sheaf into the units sheaf to verify this square. Scalar extension
preserves this equality: transpose under the pullback adjunction and evaluate on
pure generators a tensor z, which generate the scalar-extended sheaf after
sheafification. The defining normalization of finite Tate descent identifies its
exponentTransition with this root-power map. The normalized transports tr and ts
have exactly these root and generator formulas, so the argument applies to both.
Apply the degree-zero derived embedding and the shift comparison; their naturality
gives the square for shifted lines. Induct on d. At zero both transitions are the
identity and both pullback comparisons are the constant-unit comparison. At a
successor, expand baseExponentComparison and vectorIntegrationBaseCoefficientPullback.
Naturality of the derived tensor pullback moves the two coefficient maps past that
comparison. Apply the induction hypothesis to the first factor and the shifted-line
square to the second factor, then use bifunctoriality of tensor. This is the stated
square. No flatness of the finite coefficient ring is used; d=0, empty schemes,
equal exponents and ramified coefficient quotients are included. -/
theorem baseExponentComparison_pullback
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (l : Γ(Y, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (tr : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr)
    (ts : Etale.OrdinaryFiniteTwistTransport (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs) (d : ℕ) :
    (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n) f).map
        (baseExponentComparison l E n Y hY r s hrs hr hs d).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback _ (l ^ (r + 1)) hr tr f
        (by simpa only [Nat.cast_pow] using hY.pow (r + 1)) d).hom =
    (Etale.vectorIntegrationBaseCoefficientPullback _ (l ^ (s + 1)) hs ts f
        (by simpa only [Nat.cast_pow] using hY.pow (s + 1)) d).hom ≫
      (baseExponentComparison l E n X
        (by simpa using hY.map f.appTop.hom) r s hrs hr hs d).hom := by sorry

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
