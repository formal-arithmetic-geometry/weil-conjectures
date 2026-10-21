/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.ComparisonPullbackExact
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.Paper.PurityComparisonUnitInjectiveModel
import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# A normalized resolution model for global site comparison

Source: relative Kummer proof, opening paragraph, and Stacks Tags 099R, 099W,
013K, 070J, 070Y, 079P, 0DVC and 09T5
(blueprint: lem-pur-comparison-global-resolution-model).

The fixed-ring module-sheaf presentation is the one used by the recorded global
comparison. It is canonically equivalent to the coefficient-ring-sheaf presentation.
The computing isomorphisms below are determined by equations with the supplied
augmentations and the canonical right-derived comparison units.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The sheaf F in degree zero, retaining its explicit bounded-below representative.
Source: Stacks Tag 013K (blueprint: lem-pur-comparison-global-resolution-model). -/
def comparisonResolutionSingle {U : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨(CochainComplex.singleFunctor _ 0).obj F, ⟨0, inferInstance⟩⟩

/-- The two nonnegative injective resolutions, with their given augmentations.
Source: Stacks Tags 013K, 070J and 079P, applied twice as in the node's proof
(blueprint: lem-pur-comparison-global-resolution-model). -/
structure ComparisonGlobalResolution (U : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) where
  I : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))
  nonnegativeI : I.obj.IsStrictlyGE 0
  nonnegativeJ : J.obj.IsStrictlyGE 0
  injectiveI : ∀ n : ℤ, Injective (I.obj.X n)
  injectiveJ : ∀ n : ℤ, Injective (J.obj.X n)
  kInjectiveI : I.obj.IsKInjective
  kInjectiveJ : J.obj.IsKInjective
  i : comparisonResolutionSingle F ⟶ I
  t : (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapCochainComplexPlus.obj I ⟶ J
  quasiIsoI : QuasiIso i.hom
  quasiIsoT : QuasiIso t.hom

namespace ComparisonGlobalResolution

variable {U : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
  {F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
  (R : ComparisonGlobalResolution U Λ F)

/-- The adjoint h of the supplied t, using the actual comparison adjunction termwise.
Source: Stacks Tag 0DVC (blueprint: lem-pur-comparison-global-resolution-model). -/
def adjoint : R.I.obj ⟶
    ((comparisonLowerStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex (.up ℤ)).obj
      R.J.obj :=
  ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex (.up ℤ)).homEquiv
    R.I.obj R.J.obj R.t.hom

/-- The source complex of global sections of the etale resolution.
Source: Stacks Tag 099R (blueprint: lem-pur-comparison-global-resolution-model). -/
def sourceSections : CochainComplex.Plus (ModuleCat.{u + 1} Λ) :=
  (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).mapCochainComplexPlus.obj R.I

/-- The target complex of global sections of the pro-etale resolution.
Source: Stacks Tag 099R (blueprint: lem-pur-comparison-global-resolution-model). -/
def targetSections : CochainComplex.Plus (ModuleCat.{u + 1} Λ) :=
  (sheafToPresheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ) ⋙
    (evaluation _ _).obj
      (op ((Scheme.toProEt U).obj (Scheme.Etale.mk (𝟙 U))))).mapCochainComplexPlus.obj R.J

/-- Evaluation of h at the final object; restriction identifies (N J)(U) with J(U).
Source: Stacks Tags 099R and 099W
(blueprint: lem-pur-comparison-global-resolution-model). -/
def sectionMap : R.sourceSections ⟶ R.targetSections :=
  ⟨((sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
            (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).mapHomologicalComplex (.up ℤ)).map
      R.adjoint⟩

/-- The identification beta = Q(t A(i)), including exact pullback's localization factor.
Source: Stacks Tag 04JC and localization
(blueprint: lem-pur-comparison-global-resolution-model). -/
def targetIdentification :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
      (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)) ⟶
    DerivedCategory.Plus.Q.obj R.J :=
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.quotient _).obj (comparisonResolutionSingle F)) ≫
    DerivedCategory.Plus.Q.map
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapCochainComplexPlus.map R.i ≫ R.t)

end ComparisonGlobalResolution

/-- The class of a global cocycle in the localized section complex. Only the canonical
homology factorization isomorphisms occur. Source: Stacks Tag 070Y
(blueprint: lem-pur-comparison-global-resolution-model). -/
def comparisonResolutionCycleClass {Λ : Type (u + 1)} [CommRing Λ]
    (K : CochainComplex.Plus (ModuleCat.{u + 1} Λ)) (q : ℤ) (z : K.obj.cycles q) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      (DerivedCategory.Plus.Q.obj K) :=
  (DerivedCategory.homologyFunctorFactorsh _ q).inv.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K.obj)
    ((HomotopyCategory.homologyFunctorFactors _ (.up ℤ) q).inv.app K.obj
      (K.obj.homologyπ q z))

/-- The actual derived-unit global comparison on the specified degree-zero model,
with the derived identity removed by its canonical isomorphism.
Source: Stacks Tag 099W and the recorded normalized global comparison
(blueprint: lem-pur-comparison-global-resolution-model). -/
def comparisonResolutionGlobalMap (U : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv.app
      ((sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
          (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))) ≫
    (finiteComparisonGlobalSections U Λ).app
      (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))

/-- There exist two nonnegative termwise injective K-injective resolutions, and every
such pair computes the specified global comparison, including its cocycle formula.
The equations for eI and eJ uniquely specify the computing isomorphisms using i and
beta = Q(t A(i)); in particular the target identification is not freely chosen.
Source: relative Kummer proof, opening paragraph; Stacks Tags 099R and 099W
(blueprint: lem-pur-comparison-global-resolution-model).

Proof:
1. The ring-sheaf Grothendieck theorem and enough-injectives theorem give enough
injectives on both sites. Apply lem-weil-pbc-complex-injective-resolution-mono at
lower bound zero to F[0], and then to A(I). Exactness of A makes its augmentation
quasi-isomorphic and its complex nonnegative. The bounded-below injectives theorem
makes both resolutions K-injective. This proves existence.
2. For any such pair, exactness carries i to a quasi-isomorphism. Localization
therefore inverts i and t A(i); its exact-functor comparison identifies the latter
with beta. This gives precisely the target identification in the statement.
3. The termwise adjunction of lem-weil-pbc-termwise-adjunction-homotopy gives
h = N(t) eta_I. Restriction along the inclusion evaluates at the same final
object, with the same coefficient action and differential. Thus evaluation is w.
4. Since A is exact, N preserves injectives by
lem-sp-right-adjoint-preserves-injectives. Hence N(J) is also nonnegative termwise
injective. Apply lem-weil-pbc-right-derived-plus-injective to N and to the two
section functors. Their units are invertible on these computing resolutions.
Inverting the localized augmentations uniquely gives eI and eJ with the displayed
normalizations.
5. Apply lem-pur-comparison-unit-injective-model to I and t. It says
RN(Qt) eta_QI = alpha_J Qh. Naturality at Qi gives
RN(beta) eta_F[0] = alpha_J Qh Qi, with the exact-pullback factor inserted.
6. Apply derived etale sections. Naturality of its computing unit and the terminal
identification of lem-weil-pbc-derived-sections-pushforward identify this with Qw.
The comparison of lem-weil-pbc-comparison-global-cohomology is this derived unit
followed by the terminal identification. The two normalization equations therefore
give Qw eJ = eI c, for the given i and beta, for every resolution pair.
7. A chain map carries cycles to cycles and boundaries to boundaries. Applying
homology to the equation in Step 6 gives the displayed formula for every q >= 0
and every cocycle z. Evaluation of h = N(t) eta_I gives h(z) = t(A(z)). The
unit's Kan-extension class indexed by (U,id) followed by sheafification is exactly
the pulled-back terminal section; comparisonConstantRingMap identifies its unit
with 1 by lem-sf-comparison-pullback-exact. This includes q = 0, with zero incoming
degree. No step uses preservation of injectives by A. -/
theorem comparisonGlobalResolutionModel (U : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (ComparisonGlobalResolution U Λ F) ∧
      ∀ R : ComparisonGlobalResolution U Λ F,
        IsIso R.targetIdentification ∧
        ∃ (eI : DerivedCategory.Plus.Q.obj R.sourceSections ≅
            (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).rightDerivedFunctorPlus.obj
                (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)))
          (eJ : DerivedCategory.Plus.Q.obj R.targetSections ≅
            (sheafToPresheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj
                (op ((Scheme.toProEt U).obj (Scheme.Etale.mk (𝟙 U))))).rightDerivedFunctorPlus.obj
                  ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
                    (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)))),
          (eI.hom ≫
            (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).rightDerivedFunctorPlus.map
                (DerivedCategory.Plus.Q.map R.i) =
            (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).rightDerivedFunctorPlusUnit.app
                ((HomotopyCategory.Plus.quotient _).obj R.I)) ∧
          (eJ.hom ≫
            (sheafToPresheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj
                (op ((Scheme.toProEt U).obj (Scheme.Etale.mk (𝟙 U))))).rightDerivedFunctorPlus.map
                  R.targetIdentification =
            (sheafToPresheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj
                (op ((Scheme.toProEt U).obj
                  (Scheme.Etale.mk (𝟙 U))))).rightDerivedFunctorPlusUnit.app
                  ((HomotopyCategory.Plus.quotient _).obj R.J)) ∧
          (DerivedCategory.Plus.Q.map R.sectionMap ≫ eJ.hom =
            eI.hom ≫ comparisonResolutionGlobalMap U Λ F) ∧
          ∀ (q : ℕ) (z : R.sourceSections.obj.cycles (q : ℤ)),
            ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map
              (comparisonResolutionGlobalMap U Λ F))
                (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map eI.hom)
                  (comparisonResolutionCycleClass R.sourceSections q z)) =
            ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map eJ.hom)
              (comparisonResolutionCycleClass R.targetSections q
                (HomologicalComplex.cyclesMap R.sectionMap.hom q z)) ∧
            (R.adjoint.f q).hom.app (op (Scheme.Etale.mk (𝟙 U)))
                (R.sourceSections.obj.iCycles q z) =
              (R.t.hom.f q).hom.app
                (op ((Scheme.toProEt U).obj (Scheme.Etale.mk (𝟙 U))))
                ((((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).unit.app
                  (R.I.obj.X q)).hom.app (op (Scheme.Etale.mk (𝟙 U))))
                    (R.sourceSections.obj.iCycles q z)) := by
  sorry

end AlgebraicGeometry.ProEtale
