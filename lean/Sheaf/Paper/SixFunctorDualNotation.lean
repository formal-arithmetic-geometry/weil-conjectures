/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains

/-! # Coefficient dual, Verdier dual, and projection notation

Source: current blueprint main-20261015, sec-six-functors-basics,
sk-def-sf-exchanges/def-sf-pf (blueprint: def-sf-pf).

The dualizing object is the existing `SixFunctorDualityData.dualizing`, namely
exceptional inverse image of the base coefficient unit. The four Verdier duals are
`SixFunctorOperationDatum.finiteVerdier`, `.integralVerdier`, `.rationalVerdier`,
and `.commonStageVerdier`; each is the recorded internal Hom into that object.

This module supplies coefficient duality on the same finite-Tor categories by
fixing the second internal-Hom argument to their coefficient tensor unit.
All four stages use the existing internal-Hom constructions.

Projection is already `SixFunctorOperationDatum.finiteExchangeProjection` at finite
coefficients and `SixFunctorExchangeData.projectionComponent` at higher coefficients,
using the datum's `integralExchange`, `rationalExchange`, and `commonStageExchange`.
The concrete finite morphism on the larger constructible/finite-Tor domain is
`AlgebraicGeometry.ProEtale.projectionMapOfCompactification`; the supplied-domain
construction is `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage.projection`.
These are the existing chosen-compactification maps, in the direction
`Rf_! K ⊗ L ⟶ Rf_! (K ⊗ Lf^* L)`. Their coefficient and compactification comparisons
are those of the datum. A3 is a field of `SixFunctorDatum`, and concrete projection
formula theorems are forward references, rather than additional assertions here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u a b

open CategoryTheory AlgebraicGeometry Opposite

namespace WeilConjectures

/-- Internal Hom into the coefficient tensor unit on the recorded finite-Tor domain.
The bifunctor is exactly the restriction of the dependency's internal Hom; in
particular its first argument is contravariant, including on morphisms.
Source: current blueprint def-sf-pf, formula `K^∨ = RHom(K, Λ_X)`
(blueprint: def-sf-pf). -/
def sixFunctorCoefficientDual {B : Type a} [Category.{b} B]
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H : Q.FullSubcategory ⥤ B} (M : SixFunctorClosedDomain P Q H) :
    (P.FullSubcategory)ᵒᵖ ⥤ P.FullSubcategory :=
  (Functor.curry.obj
    (sixFunctorDomainHom P Q H M.homPermitted M.homDomain)).flip.obj
      M.closed.monoidal.tensorUnit

namespace SixFunctorDatum

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- Finite-coefficient dual `RHom(K, Λ_X)` on `D^b_ctf(X, A_{E,n})`.
Source: current blueprint def-sf-pf, coefficient-dual formula
(blueprint: def-sf-pf). -/
def finiteCoefficientDual (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] :
    ((S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory)ᵒᵖ ⥤
      (S.toSixFunctorOperationDatum.finiteTorDomain X).FullSubcategory :=
  sixFunctorCoefficientDual (S.finiteClosed X)

/-- Integral coefficient dual using the recorded completed coefficient operations.
Source: current blueprint def-sf-pf, coefficient-dual formula at `O_E`
(blueprint: def-sf-pf). -/
def integralCoefficientDual (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] :
    ((S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory)ᵒᵖ ⥤
      (S.toSixFunctorOperationDatum.integralFiniteTorDomain X).FullSubcategory :=
  sixFunctorCoefficientDual (S.integralClosed X)

/-- Rational coefficient dual using the recorded rationalized internal Hom.
Finite Tor is the full constructible category at field coefficients.
Source: current blueprint def-sf-pf, coefficient-dual formula at `E`
(blueprint: def-sf-pf). -/
def rationalCoefficientDual (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] :
    ((⊤ : ObjectProperty
      (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory)ᵒᵖ ⥤
      (⊤ : ObjectProperty
        (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory :=
  sixFunctorCoefficientDual (S.rationalClosed X)

/-- Algebraically closed coefficient dual using common-stage internal Hom.
Objects and arrows are formed by the dependency's common finite coefficient field
and scalar-extension comparisons, with no new choice of representatives.
Source: current blueprint def-sf-pf, coefficient-dual formula at `Qbar_l`
(blueprint: def-sf-pf). -/
def commonStageCoefficientDual (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom] :
    ((⊤ : ObjectProperty
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory)ᵒᵖ ⥤
      (⊤ : ObjectProperty
        (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)).FullSubcategory :=
  sixFunctorCoefficientDual (S.commonClosed X)

end SixFunctorDatum
end WeilConjectures
