/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.SectionDerivedPushpullNormalization
public import Sheaf.SixFunctors.OpenTensorNormalizationData
import Sheaf.Topology.ProfiniteCondensedRing
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Sheaf.CategoryTheory.SheafTensor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Section equivalence and the canonical derived open adjunction

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ; Derived Categories,
Tag 015F (blueprint: lem-pd-section-derived-open-adjunction-normalization).

The extension comparison and pullback comparison are the fixed comparisons already
in the library. The two adjunctions below independently localize the ordinary
adjunctions; neither is defined by transport through the section equivalences.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing inclusion of the open pro-etale site in the ambient site.
Source: Stacks 03DI and pro-etale localization, Part (1)
(blueprint: lem-pd-section-derived-open-adjunction-normalization). -/
abbrev openSectionObject {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (V : U.ProEt) : X.ProEt :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj V

/-- The canonical generator of the sheafified extension presheaf. The abelian
open-adjunction unit, followed by the canonical restriction identification, is
exactly the image of the summand injection indexed by the structure map of V.
Source: Stacks 03DI, the direct-sum construction and its unit
(blueprint: lem-pd-section-derived-open-adjunction-normalization). -/
def internalOpenGenerator {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : internalModules Λ U) (V : U.ProEt) (m : F.X.obj.obj (op V)) :
    ((equivalence Λ X).functor.obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj F)).val.obj
        (op (openSectionObject j V)) :=
  ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).hom.app
      ((ProEtale.openImmersionLowerShriek Ab.{u + 1} j).obj F.X)).hom.app (op V)
    (((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit.app
      F.X).hom.app (op V) m)

/-- Restrict a coefficient section to the open and apply the actual alpha_j.
Source: blueprint coefficient morphisms and Stacks 03DI, summand action
(blueprint: lem-pd-section-derived-open-adjunction-normalization). -/
def openCoefficientSection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (V : U.ProEt) (r : (ring Λ X).obj.obj (op (openSectionObject j V))) :
    (ring Λ U).obj.obj (op V) :=
  (condensedPullbackHom Λ j).hom.app (op V)
    (((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).inv.app
      (condensedRingObj Λ X)).hom.app (op V) r)

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

/-- Localize the specified internal ordinary open adjunction termwise, then express
its right adjoint through the canonical exact left-derived comparison.
Source: Stacks 015F and 03DJ
(blueprint: lem-pd-section-derived-open-adjunction-normalization). -/
def localizedInternalOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : internalDerivedExtension Λ j ⊣ internalDerivedPullback Λ j :=
  (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)).ofNatIsoRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm

/-- Localize the specified section-module ordinary open adjunction independently.
Its restriction is the exact levelwise realization of the ringed left derived pullback.
Source: Stacks 015F and 03DJ
(blueprint: lem-pd-section-derived-open-adjunction-normalization). -/
def localizedSectionOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : derivedExtension Λ j ⊣ derivedPullback Λ j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (openAdjunction Λ j)

/-- The fixed extension comparison identifies the scalar actions, ordinary Hom
bijections, exactness and independently localized derived open adjunctions.
Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ; Derived Categories,
Tag 015F (blueprint: lem-pd-section-derived-open-adjunction-normalization).

Proof, following the ten steps of the node.
1. Identify the open pro-etale site with the localized ambient site using Part (1)
   of weakly-etale localization. Use alpha_j, not the constant-ring comparisons.
   Pullback is restriction followed by scalar extension; a tensor a tensor m maps
   to a times m and the inverse sends m to 1 tensor m.
2. The abelian open adjunction identifies the underlying extension sheaves by
   sending each direct-sum generator to the same generator. Its unit is precisely
   internalOpenGenerator, the sheafified summand injection.
3. The projection-formula map sends iota_phi(r| tensor m) to r tensor iota_phi(m).
   Its inverse followed by the action therefore sends r tensor iota_phi(m) to
   iota_phi(alpha_j(r|) m). Module sheafification extends this action uniquely.
   This proves linearity of the generator comparison and both scalar equations.
4. Both ordinary Hom maps send q to m mapping to q(iota_phi(m)). Conversely each
   linear map on the slice extends uniquely through the sum and sheafification.
   They are inverse on generators, proving the ordinary Hom identity for the
   uniquely mate-normalized comparison of SectionModuleOperationsData.
5. Substitute identity and counit into that identity to obtain the two displayed
   ordinary unit and counit equations.
6. Exactness on the section side follows from localizedSystemExact and change of
   coefficients along alpha_j. Internal extension and pullback are exact by their
   defining results. The fixed section equivalences are exact. No boundedness or
   injectivity hypothesis is imposed.
7. Exact-functor factorization localizes all complexes termwise. Localize the
   ordinary adjunctions with exactDerivedAdjunction and localize their comparisons.
   The localization universal property preserves the comparison equations.
8. The resolution comparison equation in sectionDerivedPushpullNormalization
   identifies derivedPullComparison with the localized ordinary pull comparison,
   after the two exact left-derived identifications. Cancel their invertible
   resolution maps on every complex; localization gives the equality everywhere.
9. Localize Step 5's unit and counit equations and rewrite the right adjoints by
   Step 8. These are the independently localized adjunctions defined above.
10. Expand the section Hom map as R'(q) composed with its unit, insert Step 9,
    cancel R'(c inverse) against R'(c), and use naturality of b. The result is
    b composed with D(E_U) of the internal Hom map for arbitrary derived q.
    Step 9 also gives the final derived counit equation.
-/
theorem sectionDerivedOpenAdjunctionNormalization {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ (F : internalModules Λ U) (V : U.ProEt)
      (r : (ring Λ X).obj.obj (op (openSectionObject j V)))
      (m : ((equivalence Λ U).functor.obj F).val.obj (op V)),
      r • internalOpenGenerator Λ j F V m =
        internalOpenGenerator Λ j F V (openCoefficientSection Λ j V r • m) ∧
      r • ((ordinaryExtensionComparison Λ j).hom.app F).val.app
          (op (openSectionObject j V)) (internalOpenGenerator Λ j F V m) =
        ((ordinaryExtensionComparison Λ j).hom.app F).val.app
          (op (openSectionObject j V))
          (internalOpenGenerator Λ j F V (openCoefficientSection Λ j V r • m))) ∧
    (∀ (F : internalModules Λ U) (G : internalModules Λ X)
      (q : (CondensedRing.openImmersionLowerShriek Λ j).obj F ⟶ G),
      (openAdjunction Λ j).homEquiv _ _
          ((ordinaryExtensionComparison Λ j).inv.app F ≫
            (equivalence Λ X).functor.map q) =
        (equivalence Λ U).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _ q) ≫
          (pullComparison Λ j).hom.app G) ∧
    (∀ F : internalModules Λ U,
      (openAdjunction Λ j).unit.app ((equivalence Λ U).functor.obj F) =
        (equivalence Λ U).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app F) ≫
          (pullComparison Λ j).hom.app ((CondensedRing.openImmersionLowerShriek Λ j).obj F) ≫
          (pullback Λ j).map ((ordinaryExtensionComparison Λ j).hom.app F)) ∧
    (∀ G : internalModules Λ X,
      (extension Λ j).map ((pullComparison Λ j).hom.app G) ≫
          (openAdjunction Λ j).counit.app ((equivalence Λ X).functor.obj G) =
        (ordinaryExtensionComparison Λ j).inv.app ((CondensedRing.upperStar Λ j).obj G) ≫
          (equivalence Λ X).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app G)) ∧
    PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j) ∧
    PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ j) ∧
    PreservesFiniteLimits (CondensedRing.upperStar Λ j) ∧
    PreservesFiniteColimits (CondensedRing.upperStar Λ j) ∧
    PreservesFiniteLimits (extension Λ j) ∧
    PreservesFiniteColimits (extension Λ j) ∧
    PreservesFiniteLimits (pullback Λ j) ∧
    PreservesFiniteColimits (pullback Λ j) ∧
    (∀ (K : DerivedCategory (internalModules Λ U))
      (M : DerivedCategory (internalModules Λ X))
      (q : (internalDerivedExtension Λ j).obj K ⟶ M),
      (localizedSectionOpenAdjunction Λ j).homEquiv _ _
          ((derivedExtensionComparison Λ j).inv.app K ≫
            (derivedEquivalence Λ X).functor.map q) =
        (derivedEquivalence Λ U).functor.map
            ((localizedInternalOpenAdjunction Λ j).homEquiv _ _ q) ≫
          (derivedPullComparison Λ j).hom.app M) ∧
    (∀ K : DerivedCategory (internalModules Λ U),
      (localizedSectionOpenAdjunction Λ j).unit.app ((derivedEquivalence Λ U).functor.obj K) =
        (derivedEquivalence Λ U).functor.map
            ((localizedInternalOpenAdjunction Λ j).unit.app K) ≫
          (derivedPullComparison Λ j).hom.app ((internalDerivedExtension Λ j).obj K) ≫
          (derivedPullback Λ j).map ((derivedExtensionComparison Λ j).hom.app K)) ∧
    (∀ M : DerivedCategory (internalModules Λ X),
      (derivedExtension Λ j).map ((derivedPullComparison Λ j).hom.app M) ≫
          (localizedSectionOpenAdjunction Λ j).counit.app
            ((derivedEquivalence Λ X).functor.obj M) =
        (derivedExtensionComparison Λ j).inv.app ((internalDerivedPullback Λ j).obj M) ≫
          (derivedEquivalence Λ X).functor.map
            ((localizedInternalOpenAdjunction Λ j).counit.app M)) := by
  sorry

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
