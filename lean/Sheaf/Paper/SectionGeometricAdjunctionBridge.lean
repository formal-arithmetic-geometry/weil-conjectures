/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module
public import Sheaf.Paper.SectionDerivedPushpullNormalization
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Topology.ProfiniteCondensedRing
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
/-! # The section-derived geometric adjunction and cartesian coefficients
Source: Stacks Project, derived.tex, Tags 09T5 and 0FND;
sites-modules.tex, Tags 03D6 and 03D7; sites-cohomology.tex, Tag 07A6
(blueprint: lem-sfb-section-geometric-adjunction-bridge).
The coefficient identification is fixed by its adjunct on every section. Ordinary
comparisons retain the identity on direct-image sections and the specified adjunction
mate on pullback. Derived comparisons retain the universal resolution transformations.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
-- Fix inference at the existing small-site coefficient universe while declaring the helpers.
attribute [-instance] WeilConjectures.integralCoefficientRingSheafify
section GeometricAdjunctionOperations
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w

namespace AlgebraicGeometry.Scheme

/-- The ordinary unbounded localization instance, retaining the fixed module category.
Source: Stacks 05RU (blueprint: lem-sfb-section-geometric-adjunction-bridge). -/
abbrev proEtaleRingDerivedLocalization (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  HasDerivedCategory.{w} (proEtaleRingModules X R)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})

variable (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  [proEtaleRingDerivedLocalization.{u, w} Y R]
  [proEtaleRingDerivedLocalization.{u, w} X S]

/-- Exact termwise pullback in the chosen ordinary unbounded derived categories.
Source: Stacks 05RU and 09T5 (blueprint: lem-sfb-section-geometric-adjunction-bridge). -/
abbrev proEtaleRingDerivedPullbackOfUniverses :
    DerivedCategory (proEtaleRingModules Y R) ⥤ DerivedCategory (proEtaleRingModules X S) :=
  (proEtaleRingModulePullback f R S c).mapDerivedCategory

/-- K-injective direct image in the same chosen derived categories.
Source: Stacks 070K and 07A6 (blueprint: lem-sfb-section-geometric-adjunction-bridge). -/
abbrev proEtaleRingDerivedDirectImageOfUniverses :
    DerivedCategory (proEtaleRingModules X S) ⥤ DerivedCategory (proEtaleRingModules Y R) :=
  (proEtaleRingModuleDirectImage f R S c).rightDerivedFunctor

/-- The derived adjunction of the specified tensor-unit-normalized ordinary adjunction.
Source: Stacks 09T5 and 07A6 (blueprint: lem-sfb-section-geometric-adjunction-bridge). -/
abbrev proEtaleRingDerivedAdjunctionOfUniverses :
    proEtaleRingDerivedPullbackOfUniverses f R S c ⊣
      proEtaleRingDerivedDirectImageOfUniverses f R S c :=
  (proEtaleRingModuleAdjunction f R S c).mapDerivedCategoryRightDerivedAdjunction

end AlgebraicGeometry.Scheme

end GeometricAdjunctionOperations
attribute [local instance] WeilConjectures.integralCoefficientRingSheafify

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable [∀ T : Scheme.{u}, proEtaleRingDerivedLocalization.{u, u + 1} T (ring Λ T)]
/-- The two specified geometric adjunctions agree with their representative normalization.
Source: Stacks 09T5, 0FND, 03D6, 03D7 and 07A6
(blueprint: lem-sfb-section-geometric-adjunction-bridge).
Proof: (1) Use internal_module_operations_transport and the ringed module adjunction
calculation to identify both ordinary pullbacks with extension after inverse image.
The fixed adjunct coefficient map gives the identity on direct-image sections; its
adjunction mate fixes the pullback comparison, including the ordinary Hom bijection.
(2) module_pullback_additive_exact and the exact section equivalences imply exactness
of both pullbacks. exactFunctor_derivedFunctor identifies their exact descents with
the universal ringed left derived functor, compatibly with its comparison at every
complex, by uniqueness of left derived functors. Naturality gives its equation on any
quasi-isomorphism t:P -> M, including each K-flat resolution.
(3) Functorial K-injective resolutions exist on the small sites. The K-injective total
derived theorem makes both right comparisons invertible on I. Uniqueness of right
derived functors identifies them compatibly with beta_I; the resolution identification
is beta_I followed by the inverse of G(Qs). Homotopy invariance makes it independent
of the resolution.
(4) Apply preDerivedAdjunctionGeneral to the common ordinary adjunction. Its fraction
formula is inv(Qt) followed by Qh and the resolution identification on the source,
and inv(Q(f*t)) followed by Q(h-flat) and inv(Qs) on the target. The ringed derived
adjunction has this same counit: take t=s=1 and h=1 at a K-injective complex in the
formula and use Adjunction.derived and its counit compatibility.
(5) The exact left adjoint's right adjoint preserves K-injectives. The K-injective
Hom theorem shows that these representatives already cover every morphism with t=1.
Thus the Hom bijections agree everywhere, and so do their units and counits.
(6) Compose with sectionDerivedPushpullNormalization and its fixed D(E) comparisons.
This identifies the internal transported adjunction with the operation adjunction.
All arguments concern ordinary unbounded derived categories; no properness is used. -/
theorem sectionGeometricAdjunctionBridge {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (ring Λ Y) ≅ ring Λ X,
      (∀ (V : Y.ProEtᵒᵖ) (r : (ring Λ Y).obj.obj V),
        ((proEtaleRingDirectImageMap f (ring Λ Y) (ring Λ X) c).hom.app V).hom r =
          ((coefficientMap Λ f).hom.app V).hom r) ∧
      ∃ (b : pullback Λ f ≅ proEtaleRingModulePullback f (ring Λ Y) (ring Λ X) c)
        (d : pushforward Λ f ≅ proEtaleRingModuleDirectImage f (ring Λ Y) (ring Λ X) c)
        (l : derivedPullback Λ f ≅
          proEtaleRingDerivedPullbackOfUniverses f (ring Λ Y) (ring Λ X) c)
        (r : derivedPushforward Λ f ≅
          proEtaleRingDerivedDirectImageOfUniverses f (ring Λ Y) (ring Λ X) c),
        (∀ (N : modules Λ X) (V : Y.ProEtᵒᵖ)
          (m : ((pushforward Λ f).obj N).val.obj V), (d.hom.app N).val.app V m = m) ∧
        (∀ (M : modules Λ Y) (N : modules Λ X) (h : (pullback Λ f).obj M ⟶ N),
          (adjunction Λ f).homEquiv M N h ≫ d.hom.app N =
            (proEtaleRingModuleAdjunction f (ring Λ Y) (ring Λ X) c).homEquiv M N
              (b.inv.app M ≫ h)) ∧
        PreservesFiniteLimits (pullback Λ f) ∧
        PreservesFiniteColimits (pullback Λ f) ∧
        PreservesFiniteLimits (proEtaleRingModulePullback f (ring Λ Y) (ring Λ X) c) ∧
        PreservesFiniteColimits (proEtaleRingModulePullback f (ring Λ Y) (ring Λ X) c) ∧
        (∀ M : CochainComplex (modules Λ Y) ℤ,
          l.hom.app (DerivedCategory.Q.obj M) ≫
              (proEtaleRingModulePullback f
                (ring Λ Y) (ring Λ X) c).mapDerivedCategoryFactors.hom.app M =
            (pullback Λ f).mapDerivedCategoryFactors.hom.app M ≫
              DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app M)) ∧
        (∀ M : CochainComplex (modules Λ Y) ℤ,
          IsIso ((pullback Λ f).leftDerivedFunctorCounit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj M))) ∧
        (∀ I : CochainComplex (modules Λ X) ℤ,
          (pushforward Λ f).rightDerivedFunctorUnit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj I) ≫
                r.hom.app (DerivedCategory.Q.obj I) =
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d (.up ℤ)).hom.app I) ≫
              (proEtaleRingModuleDirectImage f
                (ring Λ Y) (ring Λ X) c).rightDerivedFunctorUnit.app
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) ∧
        (∀ (I : CochainComplex (modules Λ X) ℤ) [I.IsKInjective],
          IsIso ((pushforward Λ f).rightDerivedFunctorUnit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) ∧
          IsIso ((proEtaleRingModuleDirectImage f
            (ring Λ Y) (ring Λ X) c).rightDerivedFunctorUnit.app
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) ∧
        (∀ (A : DerivedCategory (modules Λ Y)) (B : DerivedCategory (modules Λ X))
          (h : (derivedPullback Λ f).obj A ⟶ B),
          (derivedAdjunction Λ f).homEquiv A B h ≫ r.hom.app B =
            (proEtaleRingDerivedAdjunctionOfUniverses f
              (ring Λ Y) (ring Λ X) c).homEquiv A B (l.inv.app A ≫ h)) ∧
        (∀ A : DerivedCategory (modules Λ Y),
          (proEtaleRingDerivedAdjunctionOfUniverses f (ring Λ Y) (ring Λ X) c).unit.app A =
            (derivedAdjunction Λ f).unit.app A ≫
              r.hom.app ((derivedPullback Λ f).obj A) ≫
              (proEtaleRingDerivedDirectImageOfUniverses f
                (ring Λ Y) (ring Λ X) c).map (l.hom.app A)) ∧
        (∀ B : DerivedCategory (modules Λ X),
          (proEtaleRingDerivedAdjunctionOfUniverses f (ring Λ Y) (ring Λ X) c).counit.app B =
            (proEtaleRingDerivedPullbackOfUniverses f (ring Λ Y) (ring Λ X) c).map (r.inv.app B) ≫
              l.inv.app ((derivedPushforward Λ f).obj B) ≫
              (derivedAdjunction Λ f).counit.app B) ∧
        (∀ (M P : CochainComplex (modules Λ Y) ℤ)
          (K I : CochainComplex (modules Λ X) ℤ)
          (t : P ⟶ M) (s : K ⟶ I) [QuasiIso t] [QuasiIso s] [I.IsKInjective]
          (h : P ⟶ ((pushforward Λ f).mapHomologicalComplex (.up ℤ)).obj I),
          (derivedAdjunction Λ f).homEquiv _ _
              ((pullback Λ f).mapDerivedCategoryFactors.hom.app M ≫
                inv (DerivedCategory.Q.map
                  (((pullback Λ f).mapHomologicalComplex (.up ℤ)).map t)) ≫
                DerivedCategory.Q.map
                  ((((adjunction Λ f).mapHomologicalComplex (.up ℤ)).homEquiv P I).symm h) ≫
                inv (DerivedCategory.Q.map s)) =
            inv (DerivedCategory.Q.map t) ≫ DerivedCategory.Q.map h ≫
              (pushforward Λ f).rightDerivedFunctorUnit.app
                ((HomotopyCategory.quotient _ (.up ℤ)).obj I) ≫
              inv ((derivedPushforward Λ f).map (DerivedCategory.Q.map s))) ∧
        (∀ (M P : CochainComplex (modules Λ Y) ℤ)
          (K I : CochainComplex (modules Λ X) ℤ)
          (t : P ⟶ M) (s : K ⟶ I) [QuasiIso t] [QuasiIso s] [I.IsKInjective]
          (h : P ⟶ ((proEtaleRingModuleDirectImage f
            (ring Λ Y) (ring Λ X) c).mapHomologicalComplex (.up ℤ)).obj I),
          (proEtaleRingDerivedAdjunctionOfUniverses f (ring Λ Y) (ring Λ X) c).homEquiv _ _
              ((proEtaleRingModulePullback f
                (ring Λ Y) (ring Λ X) c).mapDerivedCategoryFactors.hom.app M ≫
                inv (DerivedCategory.Q.map
                  (((proEtaleRingModulePullback f
                    (ring Λ Y) (ring Λ X) c).mapHomologicalComplex (.up ℤ)).map t)) ≫
                DerivedCategory.Q.map
                  ((((proEtaleRingModuleAdjunction f
                    (ring Λ Y) (ring Λ X) c).mapHomologicalComplex (.up ℤ)).homEquiv P I).symm h) ≫
                inv (DerivedCategory.Q.map s)) =
            inv (DerivedCategory.Q.map t) ≫ DerivedCategory.Q.map h ≫
              (proEtaleRingModuleDirectImage f
                (ring Λ Y) (ring Λ X) c).rightDerivedFunctorUnit.app
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj I) ≫
              inv ((proEtaleRingDerivedDirectImageOfUniverses f
                (ring Λ Y) (ring Λ X) c).map (DerivedCategory.Q.map s))) ∧
        (∀ (A : DerivedCategory (internalModules Λ Y))
          (B : DerivedCategory (internalModules Λ X))
          (h : (internalDerivedPullback Λ f).obj A ⟶ B),
          (proEtaleRingDerivedAdjunctionOfUniverses f (ring Λ Y) (ring Λ X) c).homEquiv _ _
              (l.inv.app ((derivedEquivalence Λ Y).functor.obj A) ≫
                (derivedPullComparison Λ f).inv.app A ≫
                (derivedEquivalence Λ X).functor.map h) =
            (derivedEquivalence Λ Y).functor.map
                ((normalizationInternalAdjunction Λ f).homEquiv A B h) ≫
              (derivedPushComparison Λ f).hom.app B ≫
              r.hom.app ((derivedEquivalence Λ X).functor.obj B)) := by
  sorry
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
