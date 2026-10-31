/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility

/-! # Representing pairs for smooth compact support

Source: latest blueprint, sec-smooth-purity/sk-def-sp-representing-pair/_section.md,
Definition "Representing objects" (blueprint: sk-def-sp-representing-pair).

## Main definitions

* `AlgebraicGeometry.Etale.RepresentingPair`: the pair on the small etale sites.
* `AlgebraicGeometry.ProEtale.RepresentingPair`: the pair on the small pro-etale sites.

Both use the ordinary unbounded derived categories, the chosen compactification, and
bounded constructible finite-Tor tests. Neither the representing object nor the target
is required to be constructible. Coefficients are the universe lift of `ZMod (ℓ ^ n)`.
On the pro-etale site we use the fixed-ring module-sheaf presentation of the coefficient
category: `finiteCoefficientRealizationIsEquivalenceRing` identifies it canonically with
modules over the sheafified continuous-function ring of def-weil-pbc-proetale-modules.
No completion, adjoint, existence assertion, or uniqueness assertion enters the definition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- An ambient object and counit representing `Hom(Rf_!(-), K)` on the bounded
constructible finite-Tor tests on the small etale site. The ordered Tor interval is
uniform over all degree-zero module sheaves. The base and smoothness hypotheses are the
standing setting; they impose no constructibility condition on `object` or `K`.
Source: latest blueprint, sec-smooth-purity/sk-def-sp-representing-pair/_section.md,
entire definition (blueprint: sk-def-sp-representing-pair). -/
structure RepresentingPair (ℓ n : ℕ) [Fact ℓ.Prime] (_hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [Smooth f] (c : Compactification f)
    (K : DerivedCategoryModule (ULift.{u + 1} (ZMod (ℓ ^ n))) Y) where
  /-- The representing object is in the whole unbounded derived category on `X`. -/
  object : DerivedCategoryModule (ULift.{u + 1} (ZMod (ℓ ^ n))) X
  /-- The specified counit uses the ambient compactification functor. -/
  counit : (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n)))) c).obj object ⟶ K
  /-- For every Dctf test, the map is exactly `b ↦ Rf_!(b) ≫ counit`. -/
  map_bijective : ∀ M : DerivedCategoryModule (ULift.{u + 1} (ZMod (ℓ ^ n))) X,
    DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod (ℓ ^ n))) X M →
    (∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} (ZMod (ℓ ^ n))) X a b M) →
    Function.Bijective (fun b : M ⟶ object ↦
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n)))) c).map b ≫ counit)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- An ambient object and counit representing `Hom(Rf_!(-), K)` on the bounded
constructible finite-Tor tests on the small pro-etale site. Constructibility is intrinsic:
each cohomology sheaf is locally constant with finite module values on a finite
stratification. Tor amplitude tests every pro-etale module sheaf in degree zero.
Source: latest blueprint, sec-smooth-purity/sk-def-sp-representing-pair/_section.md,
entire definition (blueprint: sk-def-sp-representing-pair). -/
structure RepresentingPair (ℓ n : ℕ) [Fact ℓ.Prime] (_hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [Smooth f] (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n)))))) where
  /-- The representing object is in the whole unbounded derived category on `X`. -/
  object : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n)))))
  /-- The specified counit uses the ambient compactification functor. -/
  counit : (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n)))) c).obj object ⟶ K
  /-- For every Dctf test, the map is exactly `b ↦ Rf_!(b) ≫ counit`. -/
  map_bijective : ∀ M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))),
    DerivedCategory.boundedConstructibleIntrinsic (ULift.{u + 1} (ZMod (ℓ ^ n))) X M →
    (∃ a b : ℤ, a ≤ b ∧ _root_.DerivedCategory.torAmplitudeIn
      (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))) a b M) →
    Function.Bijective (fun b : M ⟶ object ↦
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n)))) c).map b ≫ counit)

end AlgebraicGeometry.ProEtale
