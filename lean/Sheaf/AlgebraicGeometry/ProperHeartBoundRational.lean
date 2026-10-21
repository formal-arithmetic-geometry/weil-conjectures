/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
- Stage-2 statement packet refreshed by group NV.
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.Paper.ModuleObjects
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.CategoryTheory.Monoidal.Mod
import Sheaf.Paper.CompletedCondensedCoefficients
import Sheaf.Paper.CartesianCoefficientsFiniteFree
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.ProperHeartBoundLattice
import Sheaf.Paper.ProperHeartBoundReduction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Proper direct-image bound for rational constructible module sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-heart-bound/
sk-lem-proper-heart-bound-rational.md (blueprint: det-proper-heart-bound-rational).

The two statements are the finite rational and algebraic-closure coefficient cases.
The integer dimension bound uses bottom for negative integers, since every nonempty
space has nonnegative Krull dimension. Thus negative bounds retain the empty-fibre case.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The proper direct-image bound for a finite subextension of Qbar_ell.
Source: blueprint main-20261015, sk-lem-proper-heart-bound-rational, finite rational case
(blueprint: det-proper-heart-bound-rational).

Proof plan, following the node:
1. If d < 0, all geometric fibres are empty. Surjectivity of field-extension spectra
   (lem-pc-field-extension-surjective) and its stability under base change
   (lem-weil-pbc-surjective-base-change) make every ordinary fibre empty, hence X empty.
   The empty-cover sheaf axiom makes all module sheaves and direct images zero.
   Otherwise put c = 2d+1. By det-proper-heart-bound-reduction it suffices to treat
   locally closed extensions by zero of lisse finite free integral lattices over every
   finite coefficient extension, their localizations, and their Qbar scalar extensions.
2. The internal-abelian-sheaf-module equivalence identifies the module-object and
   ring-sheaf-module categories, preserving underlying sheaves and injective resolutions
   (def-weil-pbc-internal-abelian-sheaf-module-equivalence). Grothendieck abelianness
   and enough injectives (lem-pur-ringed-site-grothendieck-abelian,
   lem-sp-grothendieck-enough-injectives) give nonnegative injective resolutions, which
   are K-injective (lem-sp-kinjective-computes). On an affine weakly contractible V over
   Y, exact evaluation and exact module forgetting identify sections of R^q p_* N with
   H^q of the section complex (det-pe-wc-sections-exact,
   lem-weil-pbc-module-sheaves-colimits-forgetful). Injective module sheaves are
   abelian-acyclic (lem-sc-injective-module-abelian-acyclic-zariski); the acyclic
   resolution criterion (lemma-weil-pbc-leray-acyclicity) and localization
   (lem-weil-pbc-cohomology-over-object-localization,
   lem-weil-proetale-weakly-etale-localization, clause 1) identify this with
   H^q(X_V,N restricted to X_V). This calculation is unchanged under scalar restriction.
3. Apply det-proper-heart-bound-lattice to each locally closed integral lattice.
   Its bound makes the groups of step 2 zero above c. Detection on weakly contractible
   sections (det-pe-sections-conservative, clause 3) gives zero higher direct images.
4. Properness implies qcqs: finite type is quasi-compact and the closed-immersion
   diagonal is quasi-compact (def-weil-proper-morphism, def-weil-finite-type-morphism,
   def-weil-closed-immersion, def-weil-quasi-separated-morphism). Apply
   det-proper-heart-continuity-direct-image through the module equivalence of step 2.
   Restriction along the coefficient unit is exact and colimit-preserving
   (sk-def-sfb-change-of-scalars), so continuity also holds for module-object images.
5. By sk-prop-sfb-qlbar-colimit-x and the balanced-tensor universal property
   (sk-def-sfb-change-of-scalars), inverting ell in a lattice is the filtered colimit
   of its multiplication-by-ell sequence. Continuity and step 3 give zero higher
   images above c. Step 2 identifies this with vanishing in rational coefficients.
6. For a finite extension F/K, det-prop-sfb-cartesian-coefficients-finite-free
   identifies F_X tensor N with a finite sum of copies of N as K_X-modules.
   Finite-sum continuity gives vanishing; step 2 detects it as F-module vanishing.
7. Finite extensions containing K are cofinal by finite composita. Hence Qbar_X is
   their filtered colimit (sk-prop-sfb-qlbar-colimit-x). Module forgetting creates this
   colimit (lem-weil-pbc-module-sheaves-colimits-forgetful); the balanced-tensor
   universal property commutes tensor with it. Continuity and step 6 give vanishing
   for Qbar scalar extension, with step 2 detecting it in Qbar-modules. All conditions
   of det-proper-heart-bound-reduction now hold, giving the assertion for every M.
   In the Qbar case the auxiliary initial field is Q_ell. -/
theorem isZero_higherDirectImage_rational_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (k : Type u) [Field k]
    (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))
    (hM : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  sorry

/-- The proper direct-image bound for the finite-subextension-valued condensed ring Qbar_ell.
Source: blueprint main-20261015, sk-lem-proper-heart-bound-rational, Qbar case
(blueprint: det-proper-heart-bound-rational).

Proof plan, following the node:
1. If d < 0, all geometric fibres are empty. Surjectivity of field-extension spectra
   (lem-pc-field-extension-surjective) and its stability under base change
   (lem-weil-pbc-surjective-base-change) make every ordinary fibre empty, hence X empty.
   The empty-cover sheaf axiom makes all module sheaves and direct images zero.
   Otherwise put c = 2d+1. By det-proper-heart-bound-reduction it suffices to treat
   locally closed extensions by zero of lisse finite free integral lattices over every
   finite coefficient extension, their localizations, and their Qbar scalar extensions.
2. The internal-abelian-sheaf-module equivalence identifies the module-object and
   ring-sheaf-module categories, preserving underlying sheaves and injective resolutions
   (def-weil-pbc-internal-abelian-sheaf-module-equivalence). Grothendieck abelianness
   and enough injectives (lem-pur-ringed-site-grothendieck-abelian,
   lem-sp-grothendieck-enough-injectives) give nonnegative injective resolutions, which
   are K-injective (lem-sp-kinjective-computes). On an affine weakly contractible V over
   Y, exact evaluation and exact module forgetting identify sections of R^q p_* N with
   H^q of the section complex (det-pe-wc-sections-exact,
   lem-weil-pbc-module-sheaves-colimits-forgetful). Injective module sheaves are
   abelian-acyclic (lem-sc-injective-module-abelian-acyclic-zariski); the acyclic
   resolution criterion (lemma-weil-pbc-leray-acyclicity) and localization
   (lem-weil-pbc-cohomology-over-object-localization,
   lem-weil-proetale-weakly-etale-localization, clause 1) identify this with
   H^q(X_V,N restricted to X_V). This calculation is unchanged under scalar restriction.
3. Apply det-proper-heart-bound-lattice to each locally closed integral lattice.
   Its bound makes the groups of step 2 zero above c. Detection on weakly contractible
   sections (det-pe-sections-conservative, clause 3) gives zero higher direct images.
4. Properness implies qcqs: finite type is quasi-compact and the closed-immersion
   diagonal is quasi-compact (def-weil-proper-morphism, def-weil-finite-type-morphism,
   def-weil-closed-immersion, def-weil-quasi-separated-morphism). Apply
   det-proper-heart-continuity-direct-image through the module equivalence of step 2.
   Restriction along the coefficient unit is exact and colimit-preserving
   (sk-def-sfb-change-of-scalars), so continuity also holds for module-object images.
5. By sk-prop-sfb-qlbar-colimit-x and the balanced-tensor universal property
   (sk-def-sfb-change-of-scalars), inverting ell in a lattice is the filtered colimit
   of its multiplication-by-ell sequence. Continuity and step 3 give zero higher
   images above c. Step 2 identifies this with vanishing in rational coefficients.
6. For a finite extension F/K, det-prop-sfb-cartesian-coefficients-finite-free
   identifies F_X tensor N with a finite sum of copies of N as K_X-modules.
   Finite-sum continuity gives vanishing; step 2 detects it as F-module vanishing.
7. Finite extensions containing K are cofinal by finite composita. Hence Qbar_X is
   their filtered colimit (sk-prop-sfb-qlbar-colimit-x). Module forgetting creates this
   colimit (lem-weil-pbc-module-sheaves-colimits-forgetful); the balanced-tensor
   universal property commutes tensor with it. Continuity and step 6 give vanishing
   for Qbar scalar extension, with step 2 detecting it in Qbar-modules. All conditions
   of det-proper-heart-bound-reduction now hold, giving the assertion for every M.
   In the Qbar case the auxiliary initial field is Q_ell. -/
theorem isZero_higherDirectImage_padicAlgCl_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (hchar : ringChar k ≠ 0) (hell : ringChar k ≠ ℓ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
      if d < 0 then ⊥ else (d.toNat : WithBot ℕ∞))
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M)
    (q : ℤ) (hq : 2 * d + 1 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  sorry

end AlgebraicGeometry.ProEtale
