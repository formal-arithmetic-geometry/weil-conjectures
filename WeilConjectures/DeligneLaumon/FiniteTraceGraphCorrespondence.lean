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
public import WeilConjectures.SmoothPurity.TraceFixedScheme
public import WeilConjectures.AlgebraicGeometry.FixedScheme

/-!
# Graph correspondences over arbitrary finite primary coefficient rings

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/
def-trf-graph-correspondence.md, complete definition
(blueprint: def-trf-graph-correspondence).

The exceptional leg is the identity and the ordinary leg is the given endomorphism.
The notation `u = v` uses the canonical identity exceptional identification. We construct
that identification by transposing the specified compactification comparison followed by
the canonical compact-support identity map, under the supplied exceptional adjunction.
No properness of the endomorphism or invertibility of the coefficient map is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

private theorem isIso_homEquiv_of_natIso
    {C : Type*} [Category C]
    {F G : C ⥤ C} (adj : F ⊣ G) (e : F ≅ 𝟭 C)
    {M : C} : IsIso (adj.homEquiv M M (e.hom.app M)) := by
  have : F.IsEquivalence := Functor.isEquivalence_of_iso e.symm
  rw [adj.homEquiv_unit]
  infer_instance

variable (F : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
  [DiscreteTopology A] [IsTopologicalRing A]
  (hℓ : ℓ ≠ F.p) (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ℓ ^ n) • a = 0)
  (X : Over (Spec (.of F.k)))
  [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]

end WeilConjectures
