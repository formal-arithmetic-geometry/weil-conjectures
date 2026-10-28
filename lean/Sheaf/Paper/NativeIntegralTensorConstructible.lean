/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.LocallyFiniteAdicRealizationData

/-! # Native constructibility of a finite integral tensor model

Source: Bhatt--Scholze, Proposition 6.8.11(3) and Proposition 6.8.14(2).
(blueprint: lem-sf-native-integral-tensor-constructible).
The assertion concerns the explicit derived tensor functor, independently of
any normalized functor on the common-stage category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)

attribute [local irreducible] sections CoefficientPresentation.integralMap

/-- Extension of a constructible complete integral complex to the native coefficient
has bounded constructible cohomology, read through the section-module equivalence.

Source: Bhatt--Scholze, Proposition 6.8.11(3), Proposition 6.8.14(2) and Lemma 6.8.2.
(blueprint: lem-sf-native-integral-tensor-constructible).

Proof in words: the normalized integral isomorphism identifies the completed coefficient
with continuous integral functions, and the normalized inclusion identifies the displayed
map with integral inclusion followed by the given finite-field embedding. On a finite
constructible stratification the integral complex is perfect over the completed integral
coefficient. Localization at its uniformizer is exact. The finite-field realization and
flat extension to the locally finite algebraic-closure coefficient therefore give bounded
complexes of locally finite free native modules on each stratum. Their cohomology is native
constructible: finite-dimensional coefficient kernels and cokernels are locally finite free
on a refinement, and the finite stratification globalizes the assertion. Their bounds can
be chosen from the finite-Tor interval of K over the finitely many strata.
The section-module equivalence retains
the underlying sheaves and is exact, so the given isomorphism transfers these conclusions
to M. Rank zero, the zero complex and the empty scheme satisfy the same argument.
-/
theorem nativeIntegralTensor_constructible
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [IsCommMonObj (abRing l X)] [(sections l X).Additive]
    [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]
    (E : Index l (PadicAlgCl l))
    (C : CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E))
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (M : DerivedCategory (ProEtale.AdicSheaf l X))
    (e : (sections l X).mapDerivedCategory.obj M ≅
      (pbcDerivedExtend (C.integralMap l X)).obj K.obj) :
    ProEtale.DerivedCategory.boundedAdicConstructible l X M := by sorry

end WeilConjectures.LocallyFiniteAdicRealization
