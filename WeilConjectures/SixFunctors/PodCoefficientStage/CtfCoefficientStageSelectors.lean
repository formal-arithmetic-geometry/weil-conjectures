/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates

/-! # Selectors for the four constructible coefficient stages

This file defines selectors which, for each of the four coefficient stages (finite,
integral, rational and common-stage algebraically closed), pick out the bounded
constructible category, its finite-Tor domain, the six-functor operations and the
partial tensor product.

## Implementation details

The selectors only select the supplied categories, domains and operations. No restricted
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
common-stage algebraically closed coefficients. -/
inductive PodCoefficientStage where
  | finite | integral | rational | common

namespace PodCoefficientStage
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D C E n hn)

/-- The bounded constructible category at the selected stage. -/
abbrev category (_S : SixFunctorOperationDatum D C E n hn)
    (s : PodCoefficientStage) (X : SixFunctorSpace D) : Type (u + 2) :=
  match s with
  | .finite => sixFunctorFiniteCategory D C E n hn X
  | .integral => sfIntegralConstructibleCategory C.l E X.obj.left
  | .rational => sfRationalConstructibleCategory C.l E X.obj.left
  | .common => generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left

/-- Category structures inherited from the actual coefficient categories. -/
instance categoryInstance (s : PodCoefficientStage) (X : SixFunctorSpace D) :
    Category.{u + 2} (category (_S := S) s X) := by
  cases s <;> dsimp [category] <;> infer_instance

/-- The finite-Tor predicate; field stages use the entire constructible category. -/
def domain (s : PodCoefficientStage) (X : SixFunctorSpace D) :
    ObjectProperty (category (_S := S) s X) :=
  match s with
  | .finite => S.finiteTorDomain X
  | .integral => S.integralFiniteTorDomain X
  | .rational => ⊤
  | .common => ⊤

/-- The specified pullback, direct image, compact support and exceptional functors. -/
def operations (s : PodCoefficientStage) :
    SixFunctorPushStage D (category (_S := S) s) :=
  match s with
  | .finite => S.finite
  | .integral => S.higher.integral
  | .rational => S.higher.rational
  | .common => S.closure.commonStage

/-- The recorded tensor with its second argument restricted to finite Tor.
At finite coefficients this is the canonical projection module's partial tensor. -/
def tensor (s : PodCoefficientStage) (X : SixFunctorSpace D) :
    category (_S := S) s X ⥤ (domain S s X).FullSubcategory ⥤ category (_S := S) s X :=
  match s with
  | .finite => CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X ⋙
      (Functor.whiskeringLeft _ _ _).obj
        ((finiteTorConstructible C.l E n hn X.obj.left).lift
          ((domain S .finite X).ι ⋙
            (AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible
              C.l E n hn X.obj.left).ι)
          (fun K ↦ K.property))
  | .integral => S.higher.integralTensor X ⋙
      (Functor.whiskeringLeft _ _ _).obj (domain S .integral X).ι
  | .rational => S.higher.rationalTensor X ⋙
      (Functor.whiskeringLeft _ _ _).obj (domain S .rational X).ι
  | .common => S.closure.commonStageTensor X ⋙
      (Functor.whiskeringLeft _ _ _).obj (domain S .common X).ι

end PodCoefficientStage

end WeilConjectures
