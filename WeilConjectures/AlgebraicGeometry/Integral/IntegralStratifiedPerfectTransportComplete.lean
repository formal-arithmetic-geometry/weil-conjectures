/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectTransportProfile
public import WeilConjectures.CategoryTheory.Adjunction.TowerTransitionTransport
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.AlgebraicGeometry.SmoothBaseChange.ActualCompletedReductionReconstruction
import all WeilConjectures.SmoothPurity.Completed.CompletedCoefficientCompletionRoosTransport
import all WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulReductionRoosTriangle
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison

/-! # Intrinsic completeness along isomorphisms of coefficient data

The finite reduction towers of a completed object and of its transport along the completed
isomorphism of a datum isomorphism are identified, compatibly with the transitions. A
derived-limit presentation therefore transports, and with the Roos triangle of the
completion reflector it gives intrinsic completeness.

Source: Stacks Tags 099M and 099N (auxiliary; not a blueprint node).
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

section Tower

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal) (T : Scheme.{u})

end Tower

section Complete

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal) (T : Scheme.{u})

end Complete

end AlgebraicGeometry.Scheme
