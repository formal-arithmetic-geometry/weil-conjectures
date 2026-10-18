/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.CompleteProetale
public import Sheaf.Paper.UniformCompleteTriangulated
import Sheaf.Paper.PreservationConstructible
import Sheaf.Paper.CompletedExchangeCoherence
import Sheaf.RingTheory.UniformPerfectQuotientBound
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.KFlat
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.ProEtaleStalkConservative
import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CompletedPullback
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.PbcUniformCompleteTriangulated

/-! # Constructible complete proper base change

Source: blueprint order 1356; Stacks 09C9 and 09C1
(blueprint: cor-weil-pbc-constructible-complete).
The full category and its actual completed coefficient ring are the published ones.
All components are the specified ordered-composite exchange of the coefficient datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A]
variable {X' X Y' Y : Scheme.{u}}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The source composite of the published ordinary direct image and completed pullback.
Source: blueprint order 1356 (blueprint: cor-weil-pbc-constructible-complete). -/
abbrev constructibleCompleteSource (f : X ⟶ Y) (g : Y' ⟶ Y)
    (d : AdicCoefficientDatum A) := d.push f ⋙ d.completedPull g

/-- The target composite of the published completed pullback and ordinary direct image.
Source: blueprint order 1356 (blueprint: cor-weil-pbc-constructible-complete). -/
abbrev constructibleCompleteTarget (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (d : AdicCoefficientDatum A) := d.completedPull g' ⋙ d.push f'

/-- Exactly the published ordered-composite exchange, with its actual coefficient action.
Source: blueprint order 1356 (blueprint: cor-weil-pbc-constructible-complete). -/
abbrev constructibleCompleteExchangeComponent
    (sq : ChosenCartesianSquare g' f' f g) (d : AdicCoefficientDatum A)
    (K : d.derived X) :
    (constructibleCompleteSource f g d).obj K ⟶
      (constructibleCompleteTarget g' f' d).obj K :=
  d.completedExchange sq K

/-- Proper base change restricts to a natural isomorphism of ordinary triangulated
functors on the recorded full bounded constructible complete subcategories. The last
equality identifies every component definitionally with AdicCoefficientDatum.completedExchange,
the very morphism whose invertibility completeProetale_isIso asserts.
Source: blueprint order 1356; Stacks 09C9 and 09C1
(blueprint: cor-weil-pbc-constructible-complete).
Proof:
1. Membership supplies intrinsic completeness and compatible retained etale origins.
Apply completeProetale_isIso to the specified completed exchange component.
2. Uniform local models in [d0,d1] and the common perfect-quotient resolution in
[-r,0] give the common reduction interval [d0-r,d1]. Detect vanishing on each
stratum cover and then on etale-origin cohomology stalks; the strata need not cover
in the pro-etale topology.
3. Apply pbc_preservation_constructible to this interval. Both displayed endpoints,
as well as the two intermediate outputs, satisfy all three membership clauses.
4. pbcUniformComplete_isTriangulated supplies the inherited triangulations. Reduction
and strict tower pullback are exact total left derivations, and Rlim and direct image
are exact total right derivations. Their composites restrict through the full
subcategories, retaining the ambient maps, shift comparisons and triangles.
5. Naturality of the specified completed exchange holds for every morphism.
Fullness retains its components and their inverses. The naturality equality implies
naturality of the inverse by multiplying by the inverse components on both sides.
Thus these exact functors have the asserted natural isomorphism with precisely the
specified components, without requiring functorial cones in an ordinary category. -/
theorem constructibleComplete_properBaseChange
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
    (N : ℕ) (_hN : 0 < N)
    (_hAnn : (N : Padic.coefficientExtensionRing l E 1) = 0)
    (_hNX : IsUnit (N : Γ(X, ⊤))) (_hNY : IsUnit (N : Γ(Y, ⊤)))
    (_hNX' : IsUnit (N : Γ(X', ⊤))) (_hNY' : IsUnit (N : Γ(Y', ⊤)))
    (e : ℕ)
    (_hFibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    ObjectProperty.IsTriangulated (IsPbcBoundedConstructibleComplete X l E) ∧
    ObjectProperty.IsTriangulated (IsPbcBoundedConstructibleComplete Y' l E) ∧
    ∀ [ObjectProperty.IsTriangulated (IsPbcBoundedConstructibleComplete X l E)]
      [ObjectProperty.IsTriangulated (IsPbcBoundedConstructibleComplete Y' l E)],
    ∃ (hF : ∀ K : ObjectProperty.FullSubcategory
        (IsPbcBoundedConstructibleComplete X l E),
        IsPbcBoundedConstructibleComplete Y' l E
          ((constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)).obj K.obj))
      (hG : ∀ K : ObjectProperty.FullSubcategory
        (IsPbcBoundedConstructibleComplete X l E),
        IsPbcBoundedConstructibleComplete Y' l E
          ((constructibleCompleteTarget g' f'
            (pbcPadicCoefficientDatum l E)).obj K.obj)),
    ∃ (_sF : (ObjectProperty.lift (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)) hF).CommShift ℤ)
      (_sG : (ObjectProperty.lift (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteTarget g' f' (pbcPadicCoefficientDatum l E)) hG).CommShift ℤ),
    @Functor.IsTriangulated _ _ _ _ _ _ (ObjectProperty.lift
        (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)) hF)
      _sF _ _ _ _ _ _ _ _ ∧
    @Functor.IsTriangulated _ _ _ _ _ _ (ObjectProperty.lift
        (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteTarget g' f' (pbcPadicCoefficientDatum l E)) hG)
      _sG _ _ _ _ _ _ _ _ ∧
    ∃ η : ObjectProperty.lift (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteSource f g (pbcPadicCoefficientDatum l E)) hF ≅
      ObjectProperty.lift (IsPbcBoundedConstructibleComplete Y' l E)
        (ObjectProperty.ι (IsPbcBoundedConstructibleComplete X l E) ⋙
          constructibleCompleteTarget g' f' (pbcPadicCoefficientDatum l E)) hG,
      @NatTrans.CommShift _ _ _ _ _ _ η.hom ℤ _ _ _ _sF _sG ∧
      ∀ K : ObjectProperty.FullSubcategory
        (IsPbcBoundedConstructibleComplete X l E),
        (η.hom.app K).hom =
          constructibleCompleteExchangeComponent sq (pbcPadicCoefficientDatum l E) K.obj := by
  sorry

end AlgebraicGeometry.Scheme
