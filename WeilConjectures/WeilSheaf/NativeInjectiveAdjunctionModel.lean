/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.FixedPairDerivedForgetComparison
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Native Weil adjunction and its K-injective direct-image model

Source: Stacks Project, Derived Categories, Tags 08BJ, 070Y, 070K; Injectives,
Tags 079P, 079Q; WeilSheaf/Category.lean and UpperStarLowerStarAdjunction.lean.
(blueprint: lem-sf-native-weil-injective-adjunction-model)

All complexes and resolutions are in the abelian category of native Weil sheaves.
The coefficient ring is the actual locally finite function presheaf, bundled as a sheaf.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

/-- The actual locally finite functions, with their pointwise ring operations, are a sheaf.
Source: Modules on Sites, Section 03EK; ProEtale/Adic/Ring.lean,
`adicFunctionsAlgPresheaf` (blueprint: lem-sf-native-weil-injective-adjunction-model).

Proof: forgetting the pointwise algebra to vector spaces gives the presheaf underlying
`adicConstantSheaf`. That presheaf is a sheaf by the native framework. The forgetful
functor from rings to abelian groups reflects the sheaf condition, so the same unique
local gluings are gluings of the ring presheaf. This is the coefficient identification
used in step 1 of the node, without changing the local functions or their restrictions. -/
theorem nativeAdicFunctions_isSheaf (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.ProEt.topology T)
      (ProEtale.adicFunctionsAlgPresheaf l T ⋙
        forget₂ (AlgCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))) RingCat.{u + 1}) := by
  sorry

/-- The coefficient sheaf B, with the existing pointwise algebra and restriction maps.
Source: ProEtale/Adic/Ring.lean, `adicFunctionsAlgPresheaf`; Modules on Sites, 03EK
(blueprint: lem-sf-native-weil-injective-adjunction-model). -/
noncomputable def nativeAdicCoefficientRing (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
  ⟨ProEtale.adicFunctionsAlgPresheaf l T ⋙
    forget₂ (AlgCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))) RingCat.{u + 1},
    nativeAdicFunctions_isSheaf l T⟩

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [hchar : Fact (ringChar k₀ ≠ l)]

include hchar

/-- Structural assertions for each of X and Y in the native framework.
Source: Stacks 03EK, 079B, 079P, 079Q; native Category.lean:128--150
(blueprint: lem-sf-native-weil-injective-adjunction-model).

Proof plan (node steps 1, 2, 4): an internal B-action is exactly a restriction-compatible
Omega-bilinear pairing, by lem-pc-sites-sheaf-tensor-bilinear-universal. The unit and
associativity give precisely the sectionwise B-module laws; the converse restricts
scalars along the constant Omega sheaf. Morphisms are precisely B-linear sheaf maps.
The constructions are inverse and recover the original scalar action since (s1)m=sm.
Kernels are the same local sections killed by a map, with the restricted action.
Apply lem-weil-pbc-ring-sheaves-grothendieck in the larger coefficient universe and
transfer its structure across this equivalence. The Frobenius pullback is an additive
autoequivalence by lem-sf-native-adic-pullback-frobenius-mates. Apply the structural
part of lem-sf-fixed-pair-derived-forget-comparison to the identity carrier functor:
the fixed-pair category is Grothendieck and forgetting is exact and conservative.
Finally lem-sfb-grothendieck-k-injective gives a quasi-isomorphism from every unbounded
complex to a K-injective inside this abelian fixed-pair category. -/
theorem nativeWeilCategoryModel (T : Scheme.{u})
    [T.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] :
    (∃ e : ProEtale.AdicSheaf l (T ↘ Spec (CommRingCat.of k₀)).geometricFiber ≌
        SheafOfModules.{u + 1}
          (nativeAdicCoefficientRing l (T ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      PreservesFiniteLimits e.functor) ∧
    IsGrothendieckAbelian.{u + 1}
      (ProEtale.AdicSheaf l (T ↘ Spec (CommRingCat.of k₀)).geometricFiber) ∧
    IsGrothendieckAbelian.{u + 1} (ProEtaleWeilSheaf k₀ l T) ∧
    (WeilSheaf.frobeniusPullback k₀ l T).Additive ∧
    (WeilSheaf.frobeniusPullback k₀ l T).IsEquivalence ∧
    PreservesFiniteLimits (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)) ∧
    PreservesFiniteColimits (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)) ∧
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T)).ReflectsIsomorphisms ∧
    (∀ J : CochainComplex (ProEtaleWeilSheaf k₀ l T) ℤ,
      ∃ (I : CochainComplex (ProEtaleWeilSheaf k₀ l T) ℤ) (r : J ⟶ I),
        I.IsKInjective ∧ QuasiIso r) := by
  sorry

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [hXs : IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [hYs : IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [hXt : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [hYt : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [hXq : QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [hYq : QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [hfs : IsSeparated f] [hft : LocallyOfFiniteType f] [hfq : QuasiCompact f]

include hXs hYs hXt hYt hXq hYq hfs hft hfq

/-- The actual native lifts form the additive adjunction, with the specified carriers,
and its homotopy adjunction has the unit/counit formulas of the node.
Source: native UpperStarLowerStarAdjunction.lean:99--125; Stacks Tag 08BJ
(blueprint: lem-sf-native-weil-injective-adjunction-model).

Proof plan (steps 3--5): lem-sf-native-adic-pullback-frobenius-mates identifies the
specified direct-image comparison as the mate of the inverse pullback comparison.
Apply lem-sf-fixed-pair-adjunction-lift: its unit and counit have precisely the
ordinary module-sheaf carriers. Addition of maps is inherited from carriers.
Forgetting creates the abelian structure (lem-sf-fixed-pair-created-abelian-structure,
using all limits and colimits from lem-sfb-grothendieck-filtered-finite-limits).
The exact carrier pullback and exact conservative forgetting therefore make the
lift exact. For any K-injective I and acyclic M, adjunction identifies maps M to
G I with maps F M to I, which are null-homotopic since F M is acyclic
(lem-weil-pbc-right-adjoint-preserves-kinjective). Degreewise naturality makes the
unit and counit chain maps; the triangle identities show the two displayed
transposes are inverse. Additivity and naturality transport a homotopy h to
G(h) eta and a homotopy k to epsilon F(k), so these formulas descend to the
homotopy quotient, naturally in both variables, without a boundedness condition. -/
theorem nativeWeilInjectiveAdjunctionModel :
    (ProEtaleWeilSheaf.upperStar k₀ l f).Additive ∧
    (ProEtaleWeilSheaf.lowerStar k₀ l f).Additive ∧
    PreservesFiniteLimits (ProEtaleWeilSheaf.upperStar k₀ l f) ∧
    PreservesFiniteColimits (ProEtaleWeilSheaf.upperStar k₀ l f) ∧
    (ProEtaleWeilSheaf.lowerStar k₀ l f).PreservesKInjectiveComplexes ∧
    (∀ M : ProEtaleWeilSheaf k₀ l Y,
      ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f).unit.app M).hom.f =
        (ProEtale.adicUpperStarLowerStarAdjunction l
          (Scheme.Hom.geometricFiberMap f (comp_over f _))).unit.app M.carrier) ∧
    (∀ I : ProEtaleWeilSheaf k₀ l X,
      ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f).counit.app I).hom.f =
        (ProEtale.adicUpperStarLowerStarAdjunction l
          (Scheme.Hom.geometricFiberMap f (comp_over f _))).counit.app I.carrier) ∧
    (∀ (M : HomotopyCategory (ProEtaleWeilSheaf k₀ l Y) (ComplexShape.up ℤ))
      (I : HomotopyCategory (ProEtaleWeilSheaf k₀ l X) (ComplexShape.up ℤ)),
      (∀ a : ((ProEtaleWeilSheaf.upperStar k₀ l f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj M ⟶ I,
        ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f).mapHomotopyCategory
          (ComplexShape.up ℤ)).homEquiv M I a =
        ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app M ≫
          ((ProEtaleWeilSheaf.lowerStar k₀ l f).mapHomotopyCategory
            (ComplexShape.up ℤ)).map a) ∧
      (∀ b : M ⟶ ((ProEtaleWeilSheaf.lowerStar k₀ l f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj I,
        (((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f).mapHomotopyCategory
          (ComplexShape.up ℤ)).homEquiv M I).symm b =
        ((ProEtaleWeilSheaf.upperStar k₀ l f).mapHomotopyCategory
          (ComplexShape.up ℤ)).map b ≫
          ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f).mapHomotopyCategory
            (ComplexShape.up ℤ)).counit.app I)) := by
  sorry

/-- The actual ambient direct image is the universal total right derivation and is
computed by the specified formula on every native K-injective resolution.
Source: Stacks Tags 070Y, 070K; the right-derived definition and native LowerStar.lean
(blueprint: lem-sf-native-weil-injective-adjunction-model).

Proof plan (steps 6--7): exact-functor descent
(lem-sf-exact-functor-derived-triangulated) gives the ambient pullback D(F0).
The additive homotopy functor of G0 and localization are triangulated
(lem-trf-additive-homotopy-triangulated, def-weil-abstract-derived-category).
Use nativeWeilCategoryModel and lem-weil-pbc-kinjective-total-derived to derive this
composite, with comparison invertible at K-injectives. The pair is the one of
def-sfb-right-derived-functor; its unit-compatible uniqueness identifies it with
the actual rightDerivedFunctor used by the framework. For any resolution r,
localization inverts r; applying Rf_* and then inverse beta_I gives c_r, an
isomorphism with exactly the displayed hom. Naturality of beta at v is the last
equation. Everything is in D of the abelian Weil categories; neither preservation
of bounded constructibility nor a derived adjunction is asserted. -/
theorem nativeWeilDerivedDirectImageModel :
    (∀ h : ∀ J : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
        ∃ (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (r : J ⟶ I),
          I.IsKInjective ∧ QuasiIso r,
      ∃! e : (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor ≅
          (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctorOfQuasiIsoResolutions h,
        (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctorUnit ≫
          Functor.whiskerLeft DerivedCategory.Qh e.hom =
        (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctorOfQuasiIsoResolutionsUnit h) ∧
    (∀ (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [I.IsKInjective],
      IsIso ((ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj I))) ∧
    (∀ (J I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) [I.IsKInjective]
      (r : J ⟶ I) [QuasiIso r],
      ∃ c : (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor.obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj J)) ≅
        DerivedCategory.Qh.obj
          (((ProEtaleWeilSheaf.lowerStar k₀ l f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj I)),
        c.hom = (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor.map
            (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map r)) ≫
          inv ((ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ _).obj I))) ∧
    (∀ (I I' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      [I.IsKInjective] [I'.IsKInjective]
      (v : (HomotopyCategory.quotient _ _).obj I ⟶
        (HomotopyCategory.quotient _ _).obj I'),
      (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj I) ≫
        (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor.map
          (DerivedCategory.Qh.map v) =
      DerivedCategory.Qh.map
          (((ProEtaleWeilSheaf.lowerStar k₀ l f).mapHomotopyCategory
            (ComplexShape.up ℤ)).map v) ≫
        (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj I')) := by
  sorry

end AlgebraicGeometry
