/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientChange.CoefficientOperationComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCompletion
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction

/-!
# Canonical coefficient comparisons for the six-functor transformations

Source: the adopted `AlgebraicGeometry.coefficientChangeCompatibility` docstring and fields.
The latest blueprint `lem-fix-operation-reduction` supplies the route on its narrower stages.
-/

@[expose] public section
set_option autoImplicit false
universe u

-- Normalize quotient coefficient instances as in IntegralCoefficients.
attribute [local instance 2000] CommRing.toRing
open CategoryTheory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.CoefficientChange

set_option hygiene false in
local notation "DE(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} A))
set_option hygiene false in
local notation "DP(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

/-- The component of the actual compact-support projection transformation. -/
noncomputable abbrev projection (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : DE(X, A)) (L : DE(Y, A)) :=
  Etale.projectionMapApp A f K L

/-- Coefficient comparisons for the canonical scalar extensions of input objects.
For general coefficient change these are isomorphisms of arrows over the new ring;
for principal reduction the displayed arrows are read back over the original ring. -/
structure TransformationComparisons : Prop where
  principalProjection {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : DE(X, A)) (L : DE(Y, A)) :
    Nonempty (Arrow.mk ((Etale.reductionModIdeal A Y (Ideal.span {a} ^ n)).map
      (projection A f K L)) ≅
      Arrow.mk ((Etale.derivedRestrictScalars (quotient A a n) Y).map
        (projection (A ⧸ Ideal.span {a} ^ n) f
          ((etaleExtension (quotient A a n) X).obj K)
          ((etaleExtension (quotient A a n) Y).obj L))))
  principalCounit {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) f).IsLeftAdjoint] (L : DE(Y, A)) :
    Nonempty (Arrow.mk ((Etale.reductionModIdeal A Y (Ideal.span {a} ^ n)).map
      ((Adjunction.ofIsLeftAdjoint
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)).counit.app L)) ≅
      Arrow.mk ((Etale.derivedRestrictScalars (quotient A a n) Y).map
        ((Adjunction.ofIsLeftAdjoint
          (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n))
      f)).counit.app ((etaleExtension (quotient A a n) Y).obj L))))
  principalUnit {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) f).IsLeftAdjoint] (K : DE(X, A)) :
    Nonempty (Arrow.mk ((Etale.reductionModIdeal A X (Ideal.span {a} ^ n)).map
      ((Adjunction.ofIsLeftAdjoint
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)).unit.app K)) ≅
      Arrow.mk ((Etale.derivedRestrictScalars (quotient A a n) X).map
        ((Adjunction.ofIsLeftAdjoint
          (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n))
      f)).unit.app ((etaleExtension (quotient A a n) X).obj K))))
  principalExchange {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) (K : DP(X, A)) :
    Nonempty (Arrow.mk
      ((_root_.DerivedCategory.reductionModIdeal (Scheme.ProEt.topology Y')
        (Ideal.span {a} ^ n)).map
        ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app K)) ≅
      Arrow.mk ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y')
        (quotient A a n)).map
        ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) sq c).app
            ((proExtension (quotient A a n) X).obj K))))
  finiteProjection {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DE(X, A ⧸ Ideal.span {a} ^ n)) (L : DE(Y, A ⧸ Ideal.span {a} ^ n))
    (hK : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) X K)
    (hL : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) Y L) :
    Nonempty (Arrow.mk
      ((etaleExtension (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) Y).map
        (projection (A ⧸ Ideal.span {a} ^ n) f K L)) ≅
      Arrow.mk (projection (A ⧸ Ideal.span {a} ^ m) f
        ((etaleExtension (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) X).obj K)
        ((etaleExtension (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) Y).obj L)))
  finiteExchange {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) {m n : ℕ} (h : m ≤ n)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f)
    (K : DP(X, A ⧸ Ideal.span {a} ^ n))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) X K) :
    Nonempty (Arrow.mk
      ((proExtension (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) Y').map
        ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) sq c).app K)) ≅
      Arrow.mk ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ m)) sq c).app
          ((proExtension (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) X).obj K)))
  scalarProjection (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E]
    [Field E'] [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E']
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DE(X, (Shrink.{u + 1} (PadicAlgCl.integers l E)))) (L : DE(Y, (Shrink.{u + 1}
      (PadicAlgCl.integers l E)))) :
    Nonempty (Arrow.mk ((etaleExtension (PadicAlgCl.integersShrinkMap l E E') Y).map
      (projection (Shrink.{u + 1} (PadicAlgCl.integers l E)) f K L)) ≅
      Arrow.mk (projection (Shrink.{u + 1} (PadicAlgCl.integers l E')) f
        ((etaleExtension (PadicAlgCl.integersShrinkMap l E E') X).obj K) ((etaleExtension
      (PadicAlgCl.integersShrinkMap l E E') Y).obj L)))
  scalarExchange (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E]
    [Field E'] [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E']
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (c : Compactification f)
    (K : DP(X, (Shrink.{u + 1} (PadicAlgCl.integers l E)))) :
    Nonempty (Arrow.mk ((proExtension (PadicAlgCl.integersShrinkMap l E E') Y').map
      ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) sq c).app K)) ≅
      Arrow.mk ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E'))) sq c).app ((proExtension
      (PadicAlgCl.integersShrinkMap l E E') X).obj K)))
  rationalProjection (l : ℕ) [Fact l.Prime] (E E' : Type) [Field E]
    [Field E'] [Algebra E (PadicAlgCl l)] [Algebra E' (PadicAlgCl l)] [Algebra E E']
    [IsScalarTower E E' (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] E'] [IsScalarTower ℚ_[l] E' (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E'] [Small.{u + 1} E] [Small.{u + 1} E']
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DE(X, (Shrink.{u + 1} (PadicAlgCl.integers l E)))) (L : DE(Y, (Shrink.{u + 1}
      (PadicAlgCl.integers l E)))) :
    Nonempty (Arrow.mk ((Etale.derivedCompleteRationalScalarExtension l E E').map
      ((DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology l E).map
        ((DerivedCategoryDerivedCompleteIntegral.completion Y.smallEtaleTopology l E).map
          (projection (Shrink.{u + 1} (PadicAlgCl.integers l E)) f K L)))) ≅
      Arrow.mk ((DerivedCategoryDerivedCompleteRational.fromIntegral Y.smallEtaleTopology
        l E').map ((DerivedCategoryDerivedCompleteIntegral.completion Y.smallEtaleTopology
          l E').map (projection (Shrink.{u + 1} (PadicAlgCl.integers l E')) f
            ((etaleExtension (PadicAlgCl.integersShrinkMap l E E') X).obj K)
            ((etaleExtension (PadicAlgCl.integersShrinkMap l E E') Y).obj L)))))

/-- Canonical coefficient comparisons preserve the transformations defining the six functors.
Source: the adopted `AlgebraicGeometry.coefficientChangeCompatibility` docstring and fields;
the latest blueprint `lem-fix-operation-reduction` final two proof paragraphs,
including the compatibility with units, counits and rationalization
(blueprint: lem-coefficient-transformation-comparisons).

Proof: compute the scalar extension and geometric pullback on a common K-flat
representative. The termwise balancing map sends a pure tensor to the same pure
tensor along either path, so it commutes with tensor associativity and the
pullback comparison. For a proper direct image take the mate of that normalized
pullback square. The mate identities identify its composites with the geometric
unit and counit. For an open immersion the coefficient comparison is the
termwise open-extension comparison, with the same unit and counit identities.
Paste the proper and open squares for the chosen compactification. These
identities show that the projection transformation and the compact-support
exchange transformation, which are built from those units, counits and tensor
comparisons, are carried to their coefficient extensions. The principal
coefficient quotient is perfect, represented by its two-term Koszul complex;
the canonical identification of its restricted scalar extension with reduction
therefore transports the projection and exchange squares to the stated
isomorphisms of arrows over the original ring. Transposing the compact-support
comparison through its specified right-adjoint adjunction gives the exceptional
comparison and its unit/counit identities, proving the two other principal
arrow isomorphisms. Between finite quotients use bounded flat models on the
constructible finite-Tor inputs. For finite p-adic scalar extension use the
finite free coefficient model. The construction of integral completion and
rationalization is functorial on these comparison diagrams, and scalar
extension commutes with their completion and localization maps. Applying these
functors to the integral projection square proves the final rational arrow
isomorphism. Every comparison used here is normalized by the original scalar
unit; no arbitrary isomorphism of restricted objects is lifted to the new ring. -/
theorem transformationComparisons : TransformationComparisons.{u} := by
  sorry

end AlgebraicGeometry.CoefficientChange
