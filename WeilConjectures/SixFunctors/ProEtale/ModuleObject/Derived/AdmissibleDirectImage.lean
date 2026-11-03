/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp

/-!
# Admissible-coefficient ordinary direct image

The open/proper argument of det-thm-sf-ctf-stability-direct-images is separate from
extension by zero, compact support, and exceptional inverse image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory.Limits

attribute [local irreducible] upperStarFromPoint Functor.rightDerivedFunctor
attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse

section OpenImage

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]

include ℓ k

end OpenImage

/-- Ordinary derived direct image preserves constructible finite-Tor objects at every
admissible coefficient stage.

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability,
det-thm-sf-ctf-stability-direct-images, proof steps 5--9
(blueprint: lem-sfb-admissible-direct-image).

Proof:
1. All schemes in the standing setting are Noetherian and qcqs. Choose a compactification
f = j ≫ p with j quasi-compact open and p proper; its intermediate scheme is again separated
of finite type over k. Ringed-topos derived pushforward composition identifies Rf_* with
Rj_* followed by Rp_* for the cartesian coefficient sheaves.
2. For finite A descend K through finiteTorComparisonNoetherian, retaining a Tor interval
[a,b]. Etale open direct-image finiteness makes Rj_*K bounded constructible. Finite
torsion etale cohomological dimension supplies a uniform bound d for j on all A-module
sheaves. Finite A-modules are finitely presented, so the finite-constant projection formula
applies. open_tor_bound_arbitrary_field gives interval [a,b+d] against every module sheaf.
ComparisonDirectImage and ComparisonTorInterval transport both conclusions to the
pro-etale site. This argument includes the zero ring and zero complex.
3. For O_E use integralOpenDirectImage. For E and the finite-subextension algebraic closure,
use integral generators, exact conservative scalar restriction, and bounded continuity of
direct image: localization commutes with Rj_* on the bounded integral generators, and finite
free scalar extension commutes with Rj_* by additivity. Pass to the degree-zero filtered
coefficient system. Exact filtered colimits preserve cohomology and the same finite
presentations. Finite cones and shifts give bounded constructibility; ctf_equals_bc gives
finite Tor amplitude. For the retained all-continuous algebraic-closure coefficient,
use the lisse integral lattices and the bounded-continuity argument directly for that
coefficient, with the same finite stratification and cohomological bounds; no uniform
finite-extension descent for its local systems is asserted. This requires the continuous
coefficient version of the integral/rational finiteness argument, rather than an
identification of the two algebraic-closure coefficient sheaves.
4. Proper direct image preserves Dctf by finiteProperLocalizing for finite coefficients,
integralProperDirectImageAndFormulas for O_E, and the rational proper direct-image theorem
for E and the algebraic closure. Use Dctf = Dbc only for integral and rational coefficients.
Apply this to the result of steps 2--3 and compose the isomorphism of step 1. Finally
transport through the ring-object isomorphism in hΛ: exact scalar equivalences preserve
finite constant presentations and all Tor tests, and commute with derived direct image.
-/
theorem constructibleFiniteTor_rightDerivedLowerStar_of_admissible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K) :
    constantModelBoundedConstructible Λ Y ((R((f)_*⟦Λ⟧)).obj K) ∧
      DerivedCategory.finiteTorAmplitude _ ((R((f)_*⟦Λ⟧)).obj K) := by
  classical
  let c := (AlgebraicGeometry.compactificationOverField k f).obj.obj
  have : QuasiCompact c.i :=
    (AlgebraicGeometry.compactificationOverField k f).obj.property
  have ho := imageCtf_admissible_open ℓ k c.i Λ hΛ ⟨K, hK⟩
  have hp := (properLocalizingHypotheses_admissible ℓ Λ hΛ k c.g).1
    ⟨_, ho⟩
  have : (constantModelBoundedConstructible Λ Y).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined Λ Y).2.1
  have e : ((R((c.i)_*⟦Λ⟧)) ⋙ R((c.g)_*⟦Λ⟧)).obj K ≅
      (R((f)_*⟦Λ⟧)).obj K := by
    simpa only [← c.comm] using (rightDerivedLowerStarComp Λ c.i c.g).app K
  exact ObjectProperty.prop_of_iso
    (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _) e hp

end AlgebraicGeometry.ProEtale.CondensedRing
