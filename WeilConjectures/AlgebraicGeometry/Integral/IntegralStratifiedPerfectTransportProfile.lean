/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectTransportDescent
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
import all WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport

/-! # Reductions and the uniform reduction profile along isomorphisms of coefficient data

Restriction of scalars along the completed isomorphism induced by a datum isomorphism
commutes with the finite reductions, up to the level isomorphisms, and with the constant
reductions, up to the constant quotient ring isomorphisms. Constructibility is invariant
under restriction along an isomorphism of constant finite coefficient rings.

Source: Bhatt--Scholze, Definition 6.5.1 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

section RingEquiv

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

end RingEquiv

section ConstantRing

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (q : Λ ≃+* Λ')

end ConstantRing

section Profile

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal)

end Profile

end AlgebraicGeometry.Scheme
