/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage

/-!
# Direct image and finite Tor amplitude without properness

Source: literature/blueprint/master/blueprint/sec-six-functors/
`sk-thm-sf-direct-image-tor-amplitude/cor-sf-direct-image-ctf-nonproper.md`
(blueprint: cor-sf-direct-image-ctf-nonproper).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- For finite coefficients over the fixed algebraic closure of a finite field, a separated
finite-type direct image preserves bounded constructibility and increases a Tor interval by at
most twice the source dimension.  No properness or compactification is assumed.

Source: literature/blueprint/master/blueprint/sec-six-functors/
`sk-thm-sf-direct-image-tor-amplitude/cor-sf-direct-image-ctf-nonproper.md`, node order 2191
(blueprint: cor-sf-direct-image-ctf-nonproper).

Proof plan: specialize the global finite-field étale direct-image vanishing statement to the
coefficient ring `A = O_E / ϖ_E^n O_E`, obtaining the uniform bound `2 * d` for all module
sheaves.  Apply the finite-Tor direct-image theorem with this bound.  Its hypotheses are exactly
the finite-field datum, the prime inequality, the finite extension and positive coefficient level,
finite type of `X` and `Y`, separated finite type of `f`, the dimension bound, and the bounded
constructible input with Tor amplitude `[a,b]`.  The theorem yields bounded constructibility of
`Rf_* K` and Tor amplitude `[a,b+2d]`; neither step assumes properness or a compactification.
-/
theorem directImageCTFNonproper
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))]
    [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b : ℤ)
    {K : DerivedCategory
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))))}
    (hK : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) X K)
    (hTor : DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X a b K) :
    DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) Y
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n))) f).rightDerivedFunctor.obj K) ∧
      DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) Y a
        (b + 2 * (d : ℤ))
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n))) f).rightDerivedFunctor.obj K) := by
  sorry

end AlgebraicGeometry.Etale

end
