/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.ClopenMateComposite
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenProjectionMate
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Localization.Predicate

/-! # Ordinary ambient clopen comparison data

Source: Stacks Project, more-etale.tex, Tag 0F7B (lemma-shriek-proper-and-open);
sites-cohomology.tex, Tag 07A7 (remark-base-change); derived.tex, Tag 015F.
The extension to the small pro-etale sites and simultaneous semilinear systems is
agent-written (blueprint: lem-sf-ambient-exact-clopen-comparison-localization).

The helpers spell out the ordinary beta/projector/compositor word and its termwise
localization. The statements identify it with the intrinsic derived word, including
its open and proper adjunction normalizations, before any system evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₁ v₂ w₁ w₂ h₁ h₂
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.AmbientClopen

/-- Exact localization of a specified ordinary transformation, with the standard
factorizations. Source: Stacks 015F; localization universal property
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def localize
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    _ _ F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex a (.up ℤ)) DerivedCategory.Q)

/-- Localize a square comparison and insert exactly the standard composition isomorphisms.
Source: Stacks 015F, 07A7
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def localizeSquare
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {B : Type v₁} [Category.{h₁} B] [Abelian B] [HasDerivedCategory.{w₁} B]
    {A : Type v₂} [Category.{h₂} A] [Abelian A] [HasDerivedCategory.{w₂} A]
    (F : C ⥤ D) (G : D ⥤ A) (H : C ⥤ B) (I : B ⥤ A)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I] (a : F ⋙ G ⟶ H ⋙ I) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ I.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).inv ≫ localize a ≫
    (Functor.mapDerivedCategoryCompIso H I).hom

/-- The first projection equation, stated at the named lift so categorical consumers
need not unfold the construction of the scheme pullback.
Source: Stacks 0F7B; the pullback universal property
(blueprint: def-sf-ambient-exact-clopen-data). -/
theorem squareLift_fst {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) (h : k ≫ p = r ≫ i) :
    StrictTower.squareLift k r p i h ≫ pullback.fst p i = k := by
  exact pullback.lift_fst k r h

/-- The second projection equation, retaining the named fibre-product lift.
Source: Stacks 0F7B; the pullback universal property
(blueprint: def-sf-ambient-exact-clopen-data). -/
theorem squareLift_snd {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) (h : k ≫ p = r ≫ i) :
    StrictTower.squareLift k r p i h ≫ pullback.snd p i = r := by
  exact pullback.lift_snd k r h

set_option allowUnsafeReducibility true in
attribute [local irreducible] StrictTower.squareLift

section Coefficients
variable (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- The underived open-unit-normalized cartesian comparison: its inverse is the
conjugate of the actual direct-image base-change map. Source: Stacks 09AE, 07A7
(blueprint: def-sf-ambient-exact-clopen-data). -/
def sheafBeta {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (i : U ⟶ X) (p : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion b]
    (sq : IsPullback a b i p) :
    openImmersionLowerShriek A i ⋙
        upperStar A p ≅
      upperStar A a ⋙
        openImmersionLowerShriek A b :=
  ((conjugateIsoEquiv
    ((openImmersionLowerShriekUpperStarAdjunction A i).comp
      (upperStarLowerStarAdjunction A p))
    ((upperStarLowerStarAdjunction A a).comp
      (openImmersionLowerShriekUpperStarAdjunction A b))).symm
    (@asIso _ _ _ _ (baseChangeMap A sq.toCommSq)
      (isIso_baseChangeMap_of_isPullback A sq))).symm

/-- The ordinary identity/zero projection onto a clopen component, using the actual
open-to-direct-image comparison. Source: Stacks 09AE
(blueprint: def-sf-ambient-exact-clopen-data). -/
def sheafProjector {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Sheaf (Scheme.ProEt.topology X) A) ⟶
      upperStar A s ⋙
        openImmersionLowerShriek A s :=
  (upperStarLowerStarAdjunction A s).unit ≫
    Functor.whiskerLeft (upperStar A s)
      (@inv _ _ _ _ (openImmersionLowerShriekToLowerStar A s)
        (isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
          A s s.isClosedEmbedding.isClosed_range))

/-- Ordinary open composition, fixed by the composite adjunction and pullback compositor.
Source: Stacks 03DI, 07A7
(blueprint: def-sf-ambient-exact-clopen-data). -/
def sheafOpenComp {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] :
    openImmersionLowerShriek A s ⋙
        openImmersionLowerShriek A b ≅
      openImmersionLowerShriek A (s ≫ b) :=
  Adjunction.leftAdjointCompIso
    (openImmersionLowerShriekUpperStarAdjunction A s)
    (openImmersionLowerShriekUpperStarAdjunction A b)
    (openImmersionLowerShriekUpperStarAdjunction A (s ≫ b))
    (upperStarComp A s b).symm

/-- Ordinary extension transport, normalized by the pullback identification and adjunction.
Source: Stacks 03DI (blueprint: def-sf-ambient-exact-clopen-data). -/
def sheafOpenCongr {U X : Scheme.{u}} {j k : U ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    openImmersionLowerShriek A j ≅
      openImmersionLowerShriek A k :=
  ((openImmersionLowerShriekUpperStarAdjunction A j).ofNatIsoRight
    (upperStarCongr A h)).leftAdjointUniq
      (openImmersionLowerShriekUpperStarAdjunction A k)

/-- The actual ordinary clopen composite beta, projection, open composition and pullback
composition, in that order. Source: Stacks 0F7B; agent ambient comparison
(blueprint: def-sf-ambient-exact-clopen-data). -/
def sheafAlpha {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    openImmersionLowerShriek A i ⋙
        upperStar A p ⟶
      upperStar A r ⋙
        openImmersionLowerShriek A k := by
  letI : IsOpenImmersion (StrictTower.squareLift k r p i h) :=
    (StrictTower.squareLift_clopen k r p i h).1
  letI : IsClosedImmersion (StrictTower.squareLift k r p i h) :=
    (StrictTower.squareLift_clopen k r p i h).2
  exact clopenMateComposite
    (openImmersionLowerShriek A i)
    (upperStar A p)
    (upperStar A (pullback.snd p i))
    (upperStar A (StrictTower.squareLift k r p i h))
    (openImmersionLowerShriek A (StrictTower.squareLift k r p i h))
    (openImmersionLowerShriek A (pullback.fst p i))
    (openImmersionLowerShriek A k)
    (upperStar A r)
    (sheafBeta A (pullback.snd p i) (pullback.fst p i) i p
      (IsPullback.of_hasPullback p i).flip).hom
    (sheafProjector A (StrictTower.squareLift k r p i h))
    ((sheafOpenComp A (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
      (sheafOpenCongr A (squareLift_fst k r p i h)).hom)
    ((upperStarComp A (StrictTower.squareLift k r p i h)
      (pullback.snd p i)).inv ≫
      (upperStarCongr A (squareLift_snd k r p i h)).hom)

end Coefficients

section Ordinary
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The underived open-unit-normalized cartesian comparison: its inverse is the
conjugate of the actual direct-image base-change map. Source: Stacks 09AE, 07A7
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def beta {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (b : U' ⟶ X')
    (i : U ⟶ X) (p : X' ⟶ X) [IsOpenImmersion i] [IsOpenImmersion b]
    (sq : IsPullback a b i p) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ≅
      upperStar (ModuleCat.{u + 1} Λ) a ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b :=
  sheafBeta (ModuleCat.{u + 1} Λ) a b i p sq

/-- The ordinary identity/zero projection onto a clopen component, using the actual
open-to-direct-image comparison. Source: Stacks 09AE
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def projector {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⟶
      upperStar (ModuleCat.{u + 1} Λ) s ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s :=
  sheafProjector (ModuleCat.{u + 1} Λ) s

/-- Ordinary open composition, fixed by the composite adjunction and pullback compositor.
Source: Stacks 03DI, 07A7
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def openComp {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (s ≫ b) :=
  sheafOpenComp (ModuleCat.{u + 1} Λ) s b

/-- Ordinary extension transport, normalized by the pullback identification and adjunction.
Source: Stacks 03DI (blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def openCongr {U X : Scheme.{u}} {j k : U ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  sheafOpenCongr (ModuleCat.{u + 1} Λ) h

/-- The actual ordinary clopen composite beta, projection, open composition and pullback
composition, in that order. Source: Stacks 0F7B; agent ambient comparison
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def alpha {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  sheafAlpha (ModuleCat.{u + 1} Λ) k r p i h

/-- The restriction word for a square of functors, with a specified open unit.
Source: Stacks 07A7; the identity restriction normalization.
(blueprint: def-sf-ambient-exact-clopen-data) -/
def restrictionNormalized
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {I : A ⥤ B} {T : B ⥤ A} {P : B ⥤ C} {J : D ⥤ C} {K : C ⥤ D}
    (R : A ⥤ D) (η : 𝟭 A ⟶ I ⋙ T) (σ : T ⋙ R ≅ P ⋙ K)
    (v : ∀ M, R.obj M ⟶ K.obj (J.obj (R.obj M)))
    (a : I ⋙ P ⟶ R ⋙ J) : Prop :=
  ∀ M, R.map (η.app M) ≫ σ.hom.app (I.obj M) ≫ K.map (a.app M) = v M

/-- Restriction normalization in an arbitrary abelian coefficient category.
Source: Stacks 0F7B and 07A7; the open-unit normalization.
The square equation is taken in the direction `r ≫ i = k ≫ p` of the pullback-square
compositor, so that `Normalized` keeps its published auxiliary proof `h.symm`.
(blueprint: def-sf-ambient-exact-clopen-data) -/
def sheafNormalized
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] (h : r ≫ i = k ≫ p)
    (a : openImmersionLowerShriek A i ⋙ upperStar A p ⟶
      upperStar A r ⋙ openImmersionLowerShriek A k) : Prop :=
  restrictionNormalized (upperStar A r)
    (openImmersionLowerShriekUpperStarAdjunction A i).unit (upperStarCompIso A h)
    (fun M ↦ (openImmersionLowerShriekUpperStarAdjunction A k).unit.app
      ((upperStar A r).obj M)) a

/-- The identity restriction condition after the open units and pullback-square compositor.
Source: Stacks 0F7B, 07A7
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def Normalized {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    (h : k ≫ p = r ≫ i)
    (a : openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) : Prop :=
  sheafNormalized (ModuleCat.{u + 1} Λ) k r p i h.symm a

/-- Exact localization, transported only by the published total/exact pullback comparisons.
Source: Stacks 015F (blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def derivedAlpha {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    ProperOpenShriek Λ i ⋙ ProperOpenPull Λ p ⟶
      ProperOpenPull Λ r ⋙ ProperOpenShriek Λ k :=
  (Functor.isoWhiskerLeft _
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) p)).hom ≫
    localizeSquare _ _ _ _ (alpha Λ k r p i h) ≫
      (Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) r).symm _).hom

end Ordinary

/-- On complexes, localized adjunction units and counits are the images of the original
ones, through the standard exact-functor factorizations. Source: Stacks 015F, 07A7
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def AdjunctionOnComplexes
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (d : F.mapDerivedCategory ⊣ G.mapDerivedCategory) : Prop :=
  (∀ K : CochainComplex C ℤ,
    d.unit.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K)) ∧
  (∀ K : CochainComplex D ℤ,
    F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app K) =
      d.counit.app (DerivedCategory.Q.obj K))

namespace Systems
open VaryingRing
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Identity on the open component, including compatible semilinear transitions.
Source: Stacks 0F7B, 07A7
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def Normalized {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    (h : k ≫ p = r ≫ i)
    (a : extension C τ i ⋙ pull C τ p ⟶ pull C τ r ⋙ extension C τ k) : Prop :=
  restrictionNormalized (pull C τ r) (moduleJAdj C τ i).unit
    (moduleSquareG C τ k r p i h)
    (fun M ↦ (moduleJAdj C τ k).unit.app ((pull C τ r).obj M)) a

/-- All comparison equalities are in the simultaneous derived system category.
`HEq` compares the two published presentations of the same canonical functors:
their ordinary pushforwards have equal ring maps, and adjoint uniqueness then
identifies the chosen inverse images and extensions. No arbitrary transport is used.
Source: Stacks 015F, 0F7B, 07A7
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def Assertion {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : Prop :=
  Normalized C τ k r p i h (moduleAlpha C τ k r p i h) ∧
  (∀ a, Normalized C τ k r p i h a → a = moduleAlpha C τ k r p i h) ∧
  HEq (localizeSquare _ _ _ _ (moduleAlpha C τ k r p i h))
    (SemilinearProperOpen.alpha C τ k r p i h) ∧
  HEq (localizeSquare _ _ _ _
    (moduleBeta C τ (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom)
    (SemilinearProperOpen.beta C τ (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom ∧
  AdjunctionOnComplexes (moduleJAdj C τ i)
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (moduleJAdj C τ i)) ∧
  AdjunctionOnComplexes (moduleJAdj C τ k)
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (moduleJAdj C τ k)) ∧
  HEq (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (moduleJAdj C τ i))
    (SemilinearProperOpen.jAdj C τ i) ∧
  HEq (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (moduleJAdj C τ k))
    (SemilinearProperOpen.jAdj C τ k) ∧
  HEq (gamma C τ k r p i h) (SemilinearProperOpen.gamma C τ k r p i h) ∧
  (∀ M : Derived C τ U,
    (gamma C τ k r p i h).app M =
      (adj C τ p).unit.app ((J C τ i).obj ((P C τ r).obj M)) ≫
        (P C τ p).map ((VaryingRing.alpha C τ k r p i h).app ((P C τ r).obj M)) ≫
        (P C τ p).map ((J C τ k).map ((adj C τ r).counit.app M)))

end Systems

section OrdinaryAssertion
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The ordinary sheaf statement, including uniqueness, exact localization, beta and
the actual localized open units and counits, and the specified proper mate.
Source: Stacks 0F7B, 07A7, 015F
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def OrdinaryAssertion {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
    (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : Prop :=
  Normalized Λ k r p i h (alpha Λ k r p i h) ∧
  (∀ a, Normalized Λ k r p i h a → a = alpha Λ k r p i h) ∧
  derivedAlpha Λ k r p i h = properOpenAlpha Λ k r p i h ∧
  (Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) p)).hom ≫
    localizeSquare _ _ _ _
      (beta Λ (pullback.snd p i) (pullback.fst p i) i p
        (IsPullback.of_hasPullback p i).flip).hom ≫
    (Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} Λ) (pullback.snd p i)).symm _).hom =
      (properOpenBeta Λ (pullback.snd p i) (pullback.fst p i) i p
        (IsPullback.of_hasPullback p i).flip).hom ∧
  AdjunctionOnComplexes
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) i) ∧
  AdjunctionOnComplexes
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) k) ∧
  (∀ M : ProperOpenDerived Λ U,
    (properOpenMate Λ k r p i h).app M =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app
        ((ProperOpenShriek Λ i).obj ((ProperOpenPush Λ r).obj M)) ≫
      (ProperOpenPush Λ p).map
        ((derivedAlpha Λ k r p i h).app ((ProperOpenPush Λ r).obj M)) ≫
      (ProperOpenPush Λ p).map ((ProperOpenShriek Λ k).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).counit.app M)))

end OrdinaryAssertion

open WeilConjectures WeilConjectures.IntegralSystemRealization

/-- The canonical positive quotient rings are finite, including their required size lift.
Source: finite-coefficient datum; Serre, Local Fields II.2
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
instance finiteScalarRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Finite (scalarRings l E n) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
  inferInstance

/-- The component formula for the proper-adjunction mate of a square transformation.
It is the unit, followed by the right adjoint applied to the square, followed by the
right adjoint applied to the counit. Naming this formula retains the category data
when it is specialized to the native coefficient categories.
Source: Stacks 07A7, adjunction transpose; naturality of the mate bijection.
(blueprint: def-sf-ambient-exact-clopen-data) -/
def properMateFormula
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (γ : R₁ ⋙ G ⟶ H ⋙ R₂) (M : B) : Prop :=
  γ.app M = b.unit.app (G.obj (R₁.obj M)) ≫
    R₂.map (α.app (R₁.obj M)) ≫ R₂.map (H.map (a.counit.app M))

/-- Transport of a square transformation along four specified functor isomorphisms.
Source: Stacks 07A7; naturality of mates under isomorphisms.
(blueprint: def-sf-ambient-exact-clopen-data) -/
def transportAlpha
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {L₂ L₂' : C ⥤ D}
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (e : L₁ ≅ L₁') (f : L₂ ≅ L₂') (g : G ≅ G') (h : H ≅ H')
    (α : G' ⋙ L₂' ⟶ L₁' ⋙ H') : G ⋙ L₂ ⟶ L₁ ⋙ H :=
  Functor.whiskerRight g.hom L₂ ≫ Functor.whiskerLeft G' f.hom ≫ α ≫
    Functor.whiskerRight e.inv H' ≫ Functor.whiskerLeft L₁ h.inv

/-- The intrinsic system clopen alpha in any of the recorded realization coordinates.
Every identification is the canonical bridge fixed by ordinary sections and adjunctions.
Source: Stacks 0F7B, 07A7
(blueprint: lem-sf-ambient-exact-clopen-comparison-localization). -/
def realizationAlpha (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (b : CanonicalBridge l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    Operations.shriek l E o i ⋙ IntegralSystemRealization.pull l E p ⟶
      IntegralSystemRealization.pull l E r ⋙ Operations.shriek l E o k :=
  transportAlpha (b.pull l E r) (b.pull l E p) (b.shriek l E i) (b.shriek l E k)
    (SemilinearProperOpen.alpha (scalarRings l E) (scalarTransitions l E) k r p i h)

end AlgebraicGeometry.ProEtale.AmbientClopen
