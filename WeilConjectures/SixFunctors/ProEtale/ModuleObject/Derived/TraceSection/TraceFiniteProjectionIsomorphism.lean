/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.PoincareDuality.ProjectionFormula

/-! # The finite-coefficient component of the canonical projection isomorphism

Source: latest blueprint prop-functor-package, clause (5), used in Step 3(d) of
lem-trf-trace-class-diagonal-pairing.proof.md.
(blueprint: lem-trf-finite-projection-isomorphism).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceSection

/-- The actual compactification projection is invertible for finite coefficients.
Source: latest blueprint prop-functor-package, clause (5), and its finite projection proof
(blueprint: lem-trf-finite-projection-isomorphism).

Proof: open extension by zero preserves bounded constructibility. Apply the finite torsion
proper projection formula to that extension and the finite-Tor second factor, using the
ordinary etale comparison for finite discrete coefficients. Its projection is the mate of
the proper counit. Compose it with the inverse canonical open tensor comparison. This
composite is precisely exceptionalProjectionMorphismOfCompactification, so it is invertible.
The argument applies to every compactification; empty schemes and zero objects give the
same isomorphisms in the zero category. No finite-Tor hypothesis on the first factor is used.
-/
theorem finiteProjectionIsomorphism
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    [Fact (ell ≠ D.p)]
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (_hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0)
    {X Y : SepFinType D.k} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} A) X.obj.left)
    (L : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj.{u} A) Y.obj.left) :
    IsIso (exceptionalProjectionMorphismOfCompactification
      (Profinite.continuousMapRingObj.{u} A) c K.obj L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.TraceSection
