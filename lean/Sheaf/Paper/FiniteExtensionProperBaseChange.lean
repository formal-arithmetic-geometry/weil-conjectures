/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.ConstructibleCompleteBaseChange
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.PbcRationalTransport
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.Paper.CompletedPullback
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.PbcQbarCompletedPullback

/-! # Proper base change over a finite extension

Source: Weil blueprint, proper base change, order 1357
(blueprint: thm-weil-pbc-finite-extension).
The rational arrow is the image of the specified completed integral exchange under
raw scalar localization. Its endpoints use the actual completed coefficient datum
of the integral corollary; no change of coefficient realization is made.

## Main definitions

- `AlgebraicGeometry.Scheme.finiteExtensionRationalExchangeComponent`: the specified arrow.

## Main statements

- `AlgebraicGeometry.Scheme.finiteExtension_properBaseChange`: every component is invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The rational component is precisely the integral completed exchange tensored with one.
The two membership proofs only place its prescribed endpoints in the full subcategory.
Raw localization has the same objects as that integral category.
Source: blueprint order 1357, specified rational exchange
(blueprint: thm-weil-pbc-finite-extension). -/
def finiteExtensionRationalExchangeComponent
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (K : PbcRationalCategory X (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E))
    (hSource : IsPbcBoundedConstructibleComplete Y' l E
      ((constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)).obj K.obj.obj))
    (hTarget : IsPbcBoundedConstructibleComplete Y' l E
      ((constructibleCompleteTarget g' f' (pbcPadicCoefficientDatum l E)).obj K.obj.obj)) :
    (pbcRationalization Y' (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E)).obj
        ⟨(constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)).obj K.obj.obj,
          hSource⟩ ⟶
    (pbcRationalization Y' (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E)).obj
        ⟨(constructibleCompleteTarget g' f' (pbcPadicCoefficientDatum l E)).obj K.obj.obj,
          hTarget⟩ :=
  (pbcRationalization Y' (pbcPadicCoefficientDatum l E)
    (Padic.coefficientExtensionUniformizer l E)).map
      (ObjectProperty.homMk
        (constructibleCompleteExchangeComponent sq (pbcPadicCoefficientDatum l E) K.obj.obj))

/-- Proper base change for the raw rational categories of a finite extension of Q_l.
The four existential membership witnesses give the restrictions of the actual direct
images and completed pullbacks to the integral constructible categories. Their rational
extensions are those of prop-weil-pbc-rational-transport. The displayed component is
exactly the extension of the completed integral exchange, including its chosen square.
Source: blueprint order 1357 (blueprint: thm-weil-pbc-finite-extension).
Proof:
1. Every raw rational object is an integral object by def-weil-pbc-rational-category.
Use cor-weil-pbc-constructible-complete on it. The integer l annihilates the first
coefficient quotient, since its valuation is less than one by
def-weil-l-adic-coefficient-extension, and is invertible on all four schemes.
2. Apply the corollary also to the identity-horizontal squares for f and f', and to
the identity-vertical squares for g and g', with fiber bound zero. For a geometric
point y' of Y', the chosen Cartesian identification identifies the fiber of f' at y'
with the fiber of f at g y', so the same bound e applies. Identity direct image does
nothing to a K-injective representative. Identity completed pullback is completion,
whose unit is invertible on complete objects by def-weil-pbc-completed-pullback.
This supplies the four membership witnesses without extracting a common cohomological
interval from local-model bounds. Inverse image and tensor take multiplication by a
to multiplication by the same constant a; inverse limits do so componentwise. For a
K-flat roof C <- P -> D, multiplication by a replaces its second arrow u by au; the
termwise operation sends this to aF(u), leaving the denominator fixed. For right
derivations, lem-weil-pbc-kinjective-hom-derived identifies a derived morphism with a
unique homotopy class between K-injective representatives. The representative of its
scalar multiple is the scalar multiple of that class, since localization is linear
and its Hom map is injective. Termwise direct image and inverse limit preserve these
scalar multiples and homotopies, independently of any choice of resolutions. Shifts
and cones of K-injectives remain K-injective by the Hom characterization. Tensor and
the additive termwise operations preserve the two finite summands and differential
in a cone. Thus the restrictions preserve shifts, triangles and scalars, and
prop-weil-pbc-rlim-functoriality supplies the derived inverse-limit operation.
Apply prop-weil-pbc-rational-transport. Localization of the composite equals the
composite of the localizations on objects and pure tensors, so its specified exchange
is exactly finiteExtensionRationalExchangeComponent.
3. Tensor the inverse integral exchange with one. The composition and identity formulas
of def-weil-linear-scalar-localization make its two composites the identity. Thus every
rational component is invertible, also for zero and uniformizer-power-torsion objects. -/
theorem finiteExtension_properBaseChange
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (_dimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (_dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_dimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (_dimY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (_hlX : IsUnit (l : Γ(X, ⊤))) (_hlY : IsUnit (l : Γ(Y, ⊤)))
    (_hlX' : IsUnit (l : Γ(X', ⊤))) (_hlY' : IsUnit (l : Γ(Y', ⊤)))
    (e : ℕ)
    (_hFibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    ∃ (hRf : ∀ K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete Y l E
          (((pbcPadicCoefficientDatum l E).push f).obj K.obj))
      (hRf' : ∀ K : PbcBoundedConstructibleComplete X' (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete Y' l E
          (((pbcPadicCoefficientDatum l E).push f').obj K.obj))
      (hLg : ∀ K : PbcBoundedConstructibleComplete Y (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete Y' l E
          (((pbcPadicCoefficientDatum l E).completedPull g).obj K.obj))
      (hLg' : ∀ K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E),
        IsPbcBoundedConstructibleComplete X' l E
          (((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj)),
    ∀ K : PbcRationalCategory X (pbcPadicCoefficientDatum l E)
        (Padic.coefficientExtensionUniformizer l E),
      IsIso (finiteExtensionRationalExchangeComponent l E sq K
        (hLg ⟨((pbcPadicCoefficientDatum l E).push f).obj K.obj.obj, hRf K.obj⟩)
        (hRf' ⟨((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj.obj,
          hLg' K.obj⟩)) := by
  sorry

end AlgebraicGeometry.Scheme
