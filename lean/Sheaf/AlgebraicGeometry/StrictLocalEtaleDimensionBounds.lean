/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.Topology.KrullDimension
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit
import Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.IrreducibleStratificationRefinement
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import WeilConjectures.SixFunctors.Finite.GlobalSections
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen
import Sheaf.Paper.StrictlyHenselianEtaleAcyclic
import Sheaf.AlgebraicGeometry.SupportLongExact
import Sheaf.CategoryTheory.ModuleRestrictionKernelComparison
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes

/-!
# Support-sensitive étale dimension bounds on a strictly local scheme

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XVII,
Propositions 3.2.1 and 3.2.2, printed pp. 268--269.
(blueprint: lem-per-strict-local-etale-dimension-bounds).

The coefficient ring is the universe lift of Z/ℓⁿ. A local scheme is written as
`Spec R`; the generic point in the integral case is `Spec (Spec R).functionField`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Support-sensitive vanishing on the puncture, vanishing with closed support,
and the generic-point bound for an integral strictly local scheme.
Source: ILO, Travaux de Gabber, Exposé XVII, Propositions 3.2.1 and 3.2.2,
printed pp. 268--269 (blueprint: lem-per-strict-local-etale-dimension-bounds).

Proof:
1. The puncture is Noetherian, quasi-compact and quasi-separated. Express its
   module sheaf as a filtered colimit of constructible sheaves using
   lem-weil-pbc-module-sheaf-colimit-constructible. Replace each source by its image:
   its kernel is constructible by lem-weil-pbc-constructible-subobjects-noetherian,
   and its cokernel is constructible by thm-constructible-serre. The images still
   have colimit F. Exact forgetting and exact geometric stalks show that their
   supports lie in the support of F. Cohomology commutes with this filtered colimit
   by lem-weil-pbc-cohomology-filtered-colimit and
   lem-weil-pbc-etale-module-cohomology-forget.
2. Refine a constructible stratification into irreducible strata. On each stratum
   the zero-stalk and nonzero-stalk loci are open, so exactly one is empty. The
   closure Z of the support is the finite union of the closures of the generic
   points of the nonzero strata. Thus its dimension r is at most e. If the sheaf
   is zero, the assertion is immediate. Otherwise Z contains the closed point.
3. The sheaf is the finite pushforward from V = Z minus the closed point by
   lem-kun-04ca and lem-fd-finite-pushforward-cohomology. Its cohomology is that of
   its restriction to V. The local quotient defining Z is excellent and strictly
   henselian by lem-exc-finite-type-localization-excellent and
   lem-weil-pbc-strictly-henselian-quotient.
4. A system of r parameters covers V by r principal affine opens. For r = 0,
   V is empty. For r positive every intersection is again affine. The affine
   bound lem-per-affine-open-strict-local-cd kills intersection cohomology above r.
   The increasing-index Cech complex has no terms in Cech degrees at least r.
   By lem-sc-cech-spectral and lem-weil-pbc-etale-cohomology-over-open all graded
   pieces in total degrees at least 2r vanish. This proves the bound at 2e for
   constructible images, and step 1 proves it for F with the original coefficients.
5. Restrict G to the puncture and use e = d. Strict-local acyclicity kills positive
   cohomology on Spec R. The support long exact sequence and
   lem-pur-module-restriction-kernel-comparison identify supported module
   cohomology with the abelian support sequence. For q > 2d both adjacent terms
   vanish. When d = 0 the puncture is empty, so the same argument applies for q > 0.
6. In the integral case the function field is the filtered colimit of the principal
   localizations at nonzero elements. The affine-limit theorem identifies its
   spectrum with their inverse limit. Descend a constructible module sheaf to an
   affine stage by lem-weil-pbc-constructible-module-limit-descent. On every later
   affine stage the affine bound kills cohomology above d. Continuity from
   lem-weil-pbc-etale-cohomology-limit-of-schemes gives the generic-point bound.
   Finally express an arbitrary module sheaf as a filtered colimit of constructible
   ones and commute cohomology with that colimit. -/
theorem strictLocal_etale_dimension_bounds
    (R : CommRingCat.{u}) [IsNoetherianRing R] [IsStrictlyHenselianLocalRing R]
    (hR : IsExcellent R) (ℓ n d : ℕ) (hℓ : ℓ.Prime) (hn : 1 ≤ n)
    (hunit : IsUnit (ℓ : R)) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (U : (Spec R).Opens)
    (hU : (U : Set (Spec R)) = ({IsLocalRing.closedPoint R} : Set (Spec R))ᶜ) :
    (∀ (F : Sheaf U.toScheme.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))) (e : ℕ),
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ U.toScheme),
        ¬ IsZero (pointedEtaleStalk F t) →
          topologicalKrullDim (closure ({U.ι (t (IsLocalRing.closedPoint Ω))} :
            Set (Spec R))) ≤ (e : WithBot ℕ∞)) →
      ∀ (q : ℤ), (2 * e : ℤ) ≤ q →
        IsZero ((cohomology AddCommGrpCat.{u + 1} U.toScheme q).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((sheafCompose U.toScheme.smallEtaleTopology
              (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
                AddCommGrpCat.{u + 1})).obj F)))) ∧
    (∀ (G : Sheaf (Spec R).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))) (q : ℤ),
      (2 * d : ℤ) < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((derivedSupportedEtaleSections (ULift.{u + 1} (ZMod (ℓ ^ n))) (Spec R) U).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ∧
    (∀ [_hI : IsIntegral (Spec R)]
      (L : Sheaf (Spec (.of (Spec R).functionField)).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))) (q : ℤ),
      (d : ℤ) < q →
        IsZero ((cohomology AddCommGrpCat.{u + 1}
          (Spec (.of (Spec R).functionField)) q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((sheafCompose (Spec (.of (Spec R).functionField)).smallEtaleTopology
                (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ℓ ^ n))))
                  AddCommGrpCat.{u + 1})).obj L)))) := by
  sorry

end AlgebraicGeometry.Etale
