/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates

/-! # Selectors for the four constructible coefficient stages

Source: current blueprint coefficient conventions and the finite-Tor domains of
sec-six-functors/sk-thm-sf-kunneth-relative/_section.md; the domains of
sec-six-functors-basics/det-thm-sf-ctf-stability-adjunctions
(blueprint: def-sf-ctf-coefficient-stage-selectors).

These are the existing selectors extracted unchanged from PodCtfAdjunctions.
They only select the supplied categories, domains and operations. No restricted
adjunction theorem or choice of a closed presentation is used to define them.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace WeilConjectures

/-- The four admissible coefficient conventions, including completed integral and
common-stage algebraically closed coefficients. Source: the coefficient conventions
(blueprint: def-sf-ctf-coefficient-stage-selectors). -/
inductive PodCoefficientStage where
  | finite | integral | rational | common

namespace PodCoefficientStage
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D C E n hn)

/-- The existing bounded constructible category at the selected stage.
Source: domains of the restricted adjunctions
(blueprint: def-sf-ctf-coefficient-stage-selectors). -/
abbrev category (_S : SixFunctorOperationDatum D C E n hn)
    (s : PodCoefficientStage) (X : SixFunctorSpace D) : Type (u + 2) :=
  match s with
  | .finite => sixFunctorFiniteCategory D C E n hn X
  | .integral => sfIntegralConstructibleCategory C.l E X.obj.left
  | .rational => sfRationalConstructibleCategory C.l E X.obj.left
  | .common => generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left

/-- The actual finite-Tor predicate; field stages use the entire constructible category.
Source: the four finite-Tor domains
(blueprint: def-sf-ctf-coefficient-stage-selectors). -/
def domain (s : PodCoefficientStage) (X : SixFunctorSpace D) :
    ObjectProperty (category (_S := S) s X) :=
  match s with
  | .finite => S.finiteTorDomain X
  | .integral => S.integralFiniteTorDomain X
  | .rational => ⊤
  | .common => ⊤

/-- The specified pullback, direct image, compact support and exceptional functors.
Source: the three adjunctions in the node
(blueprint: def-sf-ctf-coefficient-stage-selectors). -/
def operations (s : PodCoefficientStage) :
    SixFunctorPushStage D (category (_S := S) s) :=
  match s with
  | .finite => S.finite
  | .integral => S.higher.integral
  | .rational => S.higher.rational
  | .common => S.closure.commonStage

end PodCoefficientStage

end WeilConjectures
