/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModels
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile

/-! # Completed coefficients under isomorphisms of coefficient data

A ring isomorphism `φ : A ≃+* A'` carrying the ideal of one adic coefficient datum onto the
ideal of another identifies all finite quotients, hence the quotient coefficient sheaves and
their limit. Restriction of scalars along this completed isomorphism transports completed
derived objects.

Source: Bhatt--Scholze, Proposition 6.6.11 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace AdicCoefficients

variable (T : Scheme.{u})

end AdicCoefficients

section RingEquiv

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

end RingEquiv

end AlgebraicGeometry.Scheme
