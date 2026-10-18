/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# Constant-coefficient pro-etale pullback comparison

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/
pur713-def-pullback-comparison.md (blueprint: pur713-def-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/--
The composite of the canonical constant-section coefficient comparisons is the
canonical comparison for the composite morphism.
Source: the constant-section clause of
literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/
pur713-def-pullback-comparison.md (blueprint: pur713-def-pullback-comparison).
Proof: apply the defining constant-section formula for rho to k, h and h ≫ k.
The adjoint of the composite coefficient map therefore sends a constant section a
to the constant section a, just as the adjoint of c_(h ≫ k) does. A map from the
constant presheaf is determined by these sections. Its sheafification is the
constant ring sheaf, so the sheafification universal property identifies the two
adjoints. Injectivity of the inverse-image adjunction identifies the ring-sheaf
maps; an isomorphism is determined by its forward map, giving the displayed equality.
-/
theorem proEtaleConstantRingCompositeCoefficients_eq
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    proEtaleRingCompositeCoefficients h k
      (proEtaleConstantRing V A) (proEtaleConstantRing W A)
      (proEtaleConstantRing Z A)
      (proEtaleConstantRingComparison k A)
      (proEtaleConstantRingComparison h A) =
      proEtaleConstantRingComparison (h ≫ k) A := by
  sorry

/--
The canonical derived comparison for two composable morphisms with constant
coefficients, in the direction from the iterated pullback to the pullback of
the composite.
Source: the composition clause of
literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/
pur713-def-pullback-comparison.md (blueprint: pur713-def-pullback-comparison).
-/
noncomputable def proEtaleConstantRingPullbackComposition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    proEtaleConstantRingDerivedPullback A k ⋙
        proEtaleConstantRingDerivedPullback A h ≅
      proEtaleConstantRingDerivedPullback A (h ≫ k) :=
  (proEtaleCanonicalPullbackComposition h k
    (proEtaleConstantRing V A) (proEtaleConstantRing W A)
    (proEtaleConstantRing Z A)
    (proEtaleConstantRingComparison k A)
    (proEtaleConstantRingComparison h A)).symm ≪≫
    eqToIso (congrArg (fun c ↦
      proEtaleRingDerivedPullback (h ≫ k)
        (proEtaleConstantRing V A) (proEtaleConstantRing Z A) c)
      (proEtaleConstantRingCompositeCoefficients_eq h k A))

/--
The specified comparison around the Cartesian square, formed from the two
canonical composition comparisons and the equality of the two composite arrows.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/
pur713-def-pullback-comparison.md, node order 2353
(blueprint: pur713-def-pullback-comparison).
-/
noncomputable def proEtaleConstantRingPullbackComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) g ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) f' ≅
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) f ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) g' := by
  let A := Padic.coefficientExtensionRing l E n
  letI : Finite A := Padic.finite_coefficientExtensionRing l E n _hn
  let w : f' ≫ g = g' ≫ f := sq.toCommSq.w.symm
  exact proEtaleConstantRingPullbackComposition f' g A ≪≫
    eqToIso (congrArg (fun q ↦ proEtaleConstantRingDerivedPullback A q)
      w) ≪≫
    (proEtaleConstantRingPullbackComposition g' f A).symm

end AlgebraicGeometry.Scheme

end
