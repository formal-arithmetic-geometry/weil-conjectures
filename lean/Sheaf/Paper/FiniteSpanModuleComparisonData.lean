/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.RingedSiteModules

public import Sheaf.Paper.LocallyFiniteCoefficientRingRealization
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Sheaf.Paper.CartesianCoefficients
public import Sheaf.Paper.SectionDerivedPushpullNormalization
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

/-! # Data for finite-span coefficient transport

Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Lemma 6.8.2 and Remark 6.8.15;
Stacks Project, Modules on Sites, Tags 03D6 and 03D7, Derived Categories, Tags 070I,
070Y and 09T5 (blueprint: def-sf-finite-span-module-comparison-data).

The native section ring is reconstructed from the existing locally finite-span
function ring object. Its multiplication and restrictions are the native pointwise
operations. The finite-field chart equation fixes theta to the ring-realization
comparison. The ordinary adjunction is the sheafified tensor-formula adjunction,
and its derived adjunction is derived independently from that ordinary adjunction.
The witness data retain the section formulas and units fixing every comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteSpanComparison

/-- The existing abelian sheaf of locally finite-span continuous functions.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
def nativeAb (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  (weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)

/-- The existing native ring-object structure, with its head kept explicit for synthesis.
Source: Bhatt--Scholze 6.8.1 and 6.8.3; Stacks 03D7.
(blueprint: def-sf-finite-span-module-comparison-data). -/
instance nativeMon (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) : MonObj (nativeAb l X) :=
  inferInstanceAs (MonObj ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)))

/-- The section-ring reconstruction of the native pointwise function ring.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
def ring (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsCommMonObj (nativeAb l X)] :
    Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) (nativeAb l X))

/-- Sectionwise modules over the actual locally finite-span coefficient ring.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev modules (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsCommMonObj (nativeAb l X)] :=
  SheafOfModules.{u + 1} (ring l X)

/-- The recorded internal module category over the pulled-back condensed coefficient.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev internal (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  ModuleRingedComparison.internalModules (Profinite.padicAlgClRingObj l) X

/-- The recorded reconstruction equivalence for the native coefficient ring.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
def nativeEquivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsCommMonObj (nativeAb l X)] :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (nativeAb l X) ≌ modules l X :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (nativeAb l X)


/-- Reconstruct modules after restricting their action along theta inverse.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
def equivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [IsCommMonObj (nativeAb l X)]
    (theta : condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [IsMonHom theta.hom] : internal l X ≌ modules l X :=
  (Mod.comapEquivalenceOfIsIso theta.inv).trans (nativeEquivalence l X)

/-- Ordinary module direct image with its supplied coefficient action.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
def direct (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsCommMonObj (nativeAb l X)] [IsCommMonObj (nativeAb l Y)]
    (r : ring l Y ⟶ ((InternalModuleOperations.siteMap f).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring l X)) :
    modules l X ⥤ modules l Y :=
  SheafOfModules.pushforward.{u + 1} (F := InternalModuleOperations.siteMap f) r

/-- The sheafified tensor-formula module pullback for the supplied ring map.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
def inverse (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsCommMonObj (nativeAb l X)] [IsCommMonObj (nativeAb l Y)]
    (r : ring l Y ⟶ ((InternalModuleOperations.siteMap f).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring l X))
    [(PresheafOfModules.pushforward.{u + 1}
      (F := InternalModuleOperations.siteMap f) r.hom).IsRightAdjoint] :
    modules l Y ⥤ modules l X :=
  SheafOfModules.forget (ring l Y) ⋙
    PresheafOfModules.pullback.{u + 1} (F := InternalModuleOperations.siteMap f) r.hom ⋙
    PresheafOfModules.sheafification (R₀ := (ring l X).obj) (𝟙 (ring l X).obj)

/-- The specified tensor-formula ordinary module adjunction.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev adjunction (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsCommMonObj (nativeAb l X)] [IsCommMonObj (nativeAb l Y)]
    (r : ring l Y ⟶ ((InternalModuleOperations.siteMap f).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring l X))
    [(PresheafOfModules.pushforward.{u + 1}
      (F := InternalModuleOperations.siteMap f) r.hom).IsRightAdjoint] :
    inverse l f r ⊣ direct l f r :=
  SheafOfModules.PullbackConstruction.adjunction
    (F := InternalModuleOperations.siteMap f) r

/-- The inverse-image coefficient map adjoint to native function precomposition.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev rho (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv (nativeAb l Y) (nativeAb l X)).symm
    ((weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))

/-- The ordinary and derived functors and comparisons whose normalizations are stated below.
Source: Bhatt--Scholze 6.8.15; Stacks 03D7, 070Y and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
class Data (l : ℕ) [Fact l.Prime] where
  [nativeComm : ∀ X : Scheme.{u}, IsCommMonObj (nativeAb l X)]
  theta : ∀ X : Scheme.{u},
    condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X
  [thetaMon : ∀ X : Scheme.{u}, IsMonHom (theta X).hom]
  coefficientMap : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    ring l Y ⟶ ((InternalModuleOperations.siteMap f).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (ring l X)
  [presheafAdjoint : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (PresheafOfModules.pushforward.{u + 1}
      (F := InternalModuleOperations.siteMap f) (coefficientMap f).hom).IsRightAdjoint]
  [additive : ∀ X : Scheme.{u}, (equivalence l X (theta X)).functor.Additive]
  [inverse_additive : ∀ X : Scheme.{u}, (equivalence l X (theta X)).inverse.Additive]
  [hasDerived : ∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules l X)]
  [hasResolutions : ∀ X : Scheme.{u}, Abelian.HasKInjectiveResolutions (modules l X)]
  [pullAdditive : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (inverse l f (coefficientMap f)).Additive]
  [pushAdditive : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (direct l f (coefficientMap f)).Additive]
  [pullLimits : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteLimits (inverse l f (coefficientMap f))]
  [pullColimits : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteColimits (inverse l f (coefficientMap f))]
  pullComparison : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f ⋙
      (equivalence l X (theta X)).functor ≅
    (equivalence l Y (theta Y)).functor ⋙ inverse l f (coefficientMap f)
  pushComparison : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f ⋙
      (equivalence l Y (theta Y)).functor ≅
    (equivalence l X (theta X)).functor ⋙ direct l f (coefficientMap f)
  pushComposition : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    direct l f (coefficientMap f) ⋙ direct l g (coefficientMap g) ≅
      direct l (f ≫ g) (coefficientMap (f ≫ g))
  pullComposition : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    inverse l (f ≫ g) (coefficientMap (f ≫ g)) ≅
      inverse l g (coefficientMap g) ⋙ inverse l f (coefficientMap f)
  derivedPushComparison : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctor ⋙
      (equivalence l Y (theta Y)).functor.mapDerivedCategory ≅
    (equivalence l X (theta X)).functor.mapDerivedCategory ⋙
      (direct l f (coefficientMap f)).rightDerivedFunctor

attribute [instance_reducible] Data.hasDerived

attribute [instance] Data.nativeComm Data.thetaMon Data.presheafAdjoint Data.additive
  Data.inverse_additive Data.hasDerived Data.hasResolutions Data.pullAdditive Data.pushAdditive
  Data.pullLimits Data.pullColimits

end AlgebraicGeometry.ProEtale.FiniteSpanComparison

namespace AlgebraicGeometry.ProEtale.FiniteSpanComparison

universe v w

variable (l : ℕ) [Fact l.Prime] [d : Data.{u} l]

/-- The exact localization of the specified scalar transport equivalence.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev derivedEquivalence (X : Scheme.{u}) :
    DerivedCategory.{u + 1} (internal l X) ⥤ DerivedCategory.{u + 1} (modules l X) :=
  (equivalence l X (d.theta X)).functor.mapDerivedCategory

/-- The exact localization of ordinary sectionwise pullback.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev nativePull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.{u + 1} (modules l Y) ⥤ DerivedCategory.{u + 1} (modules l X) :=
  (inverse l f (d.coefficientMap f)).mapDerivedCategory

/-- The ordinary total right derived sectionwise direct image.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev nativePush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.{u + 1} (modules l X) ⥤ DerivedCategory.{u + 1} (modules l Y) :=
  (direct l f (d.coefficientMap f)).rightDerivedFunctor

/-- The exact-localization model of the canonical internal derived pullback.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev internalPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.{u + 1} (internal l Y) ⥤ DerivedCategory.{u + 1} (internal l X) :=
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).mapDerivedCategory

/-- The ordinary total right derived internal direct image.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev internalPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.{u + 1} (internal l X) ⥤ DerivedCategory.{u + 1} (internal l Y) :=
  (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctor

/-- The localization of the specified ordinary pullback comparison.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev derivedPullComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPull l f ⋙ derivedEquivalence l X ≅ derivedEquivalence l Y ⋙ nativePull l f :=
  Functor.mapDerivedCategorySquareIso (d.pullComparison f)

/-- The localization of the geometric sectionwise inverse-image compositor.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev nativePullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    nativePull l (f ≫ g) ≅ nativePull l g ⋙ nativePull l f :=
  Functor.mapDerivedCategoryNatIso (d.pullComposition f g) ≪≫
    Functor.mapDerivedCategoryCompIso (inverse l g (d.coefficientMap g))
      (inverse l f (d.coefficientMap f))

/-- The localization of the canonical internal inverse-image compositor.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev internalPullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    internalPull l (f ≫ g) ≅ internalPull l g ⋙ internalPull l f :=
  Functor.mapDerivedCategoryNatIso
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g) ≪≫
    Functor.mapDerivedCategoryCompIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)

/-- The inverse-image square obtained from the two specified compositors.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
noncomputable def square
    (C : Scheme.{u} → Type v) [∀ X : Scheme.{u}, Category.{w} (C X)]
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X)
    (pc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq g' f' f g) :
    P g ⋙ P f' ≅ P f ⋙ P g' :=
  (pc f' g).symm ≪≫ eqToIso (congrArg (fun h : X' ⟶ Y ↦ P h) s.w.symm) ≪≫ pc g' f

/-- The canonical derived internal pullback--pushforward adjunction.
Source: Stacks Project, Tags 070Y and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev internalDerivedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalPull l f ⊣ internalPush l f :=
  (CondensedRing.upperStarLowerStarAdjunction
    (Profinite.padicAlgClRingObj l) f).mapDerivedCategoryRightDerivedAdjunction

/-- The canonical derived adjunction for sectionwise modules.
Source: Stacks Project, Tags 070Y and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev nativeDerivedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    nativePull l f ⊣ nativePush l f :=
  (adjunction l f (d.coefficientMap f)).mapDerivedCategoryRightDerivedAdjunction

/-- The unit--square--counit exchange for the canonical internal adjunctions.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev internalExchange {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq g' f' f g) :
    internalPush l f ⋙ internalPull l g ⟶ internalPull l g' ⋙ internalPush l f' :=
  (mateEquiv
    (internalDerivedAdjunction l f)
    (internalDerivedAdjunction l f')
    (square (fun T ↦ DerivedCategory (internal l T))
      (internalPull l) (internalPullComp l) s).hom).natTrans

/-- The derived counit mate on sectionwise modules with their actual ring actions.
Source: Bhatt--Scholze, Definitions 6.8.1 and 6.8.3, Remark 6.8.15; Stacks 03D7 and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev nativeExchange {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq g' f' f g) :
    nativePush l f ⋙ nativePull l g ⟶ nativePull l g' ⋙ nativePush l f' :=
  (mateEquiv
    (nativeDerivedAdjunction l f)
    (nativeDerivedAdjunction l f')
    (square (fun T ↦ DerivedCategory (modules l T))
      (nativePull l) (nativePullComp l) s).hom).natTrans

/-- A bundle of the derived categories, specified functors, compositors and adjunctions.
The fields record actual categorical data and do not choose a witness of an existence theorem.
Source: Stacks Project, Tags 070Y, 09T5 and 07A7.
(blueprint: def-sf-finite-span-module-comparison-data). -/
structure DerivedComparisonFrame where
  C : Scheme.{u} → Type (u + 2)
  D : Scheme.{u} → Type (u + 2)
  [catC : ∀ X, Category.{u + 1} (C X)]
  [catD : ∀ X, Category.{u + 1} (D X)]
  E : ∀ X, C X ⥤ D X
  P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C Y ⥤ C X
  Q : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → D Y ⥤ D X
  R : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → C X ⥤ C Y
  S : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → D X ⥤ D Y
  adjP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ⊣ R f
  adjQ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Q f ⊣ S f
  pc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f
  qc : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), Q (f ≫ g) ≅ Q g ⋙ Q f
  e : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ⋙ E X ≅ E Y ⋙ Q f
  m : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), R f ⋙ E Y ⟶ E X ⋙ S f

attribute [local instance] DerivedComparisonFrame.catC DerivedComparisonFrame.catD

/-- The normalization equation for the vertical mate of a comparison bundle.
Source: Stacks Project, Tags 070Y, 09T5 and 07A7.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev DerivedComparisonFrame.MateCondition
    (a : DerivedComparisonFrame.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  (mateEquiv (a.adjP f) (a.adjQ f) (a.e f).inv).natTrans = a.m f

/-- The exchange equation for an abstract bundle of specified derived operations.
Source: Stacks Project, Tag 07A7; Bhatt--Scholze, Remark 6.8.15.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev DerivedComparisonFrame.ExchangeCondition
    (a : DerivedComparisonFrame.{u})
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq g' f' f g) (K : a.C X) : Prop :=
  (a.E Y').map ((mateEquiv (a.adjP f) (a.adjP f')
    (square (fun T ↦ a.C T) a.P a.pc s).hom).app K) ≫
      (a.m f').app ((a.P g').obj K) ≫ (a.S f').map ((a.e g').hom.app K) =
    (a.e g).hom.app ((a.R f).obj K) ≫ (a.Q g).map ((a.m f).app K) ≫
      (mateEquiv (a.adjQ f) (a.adjQ f')
        (square (fun T ↦ a.D T) a.Q a.qc s).hom).app ((a.E X).obj K)

/-- The exchange condition on a pullback square, with its commutativity extracted generically.
Source: Stacks Project, Tag 07A7; Bhatt--Scholze, Remark 6.8.15.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev DerivedComparisonFrame.PullbackExchangeCondition
    (a : DerivedComparisonFrame.{u})
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback g' f' f g) (K : a.C X) : Prop :=
  a.ExchangeCondition s.toCommSq K

/-- The bundle of canonical derived operations associated with the specified comparison data.
Every field is the operation defined above, with no additional choice or proof assumption.
Source: Stacks Project, Tags 070Y, 09T5 and 07A7.
(blueprint: def-sf-finite-span-module-comparison-data). -/
noncomputable def derivedComparisonFrame :
    DerivedComparisonFrame.{u} where
  C := fun T ↦ DerivedCategory.{u + 1} (internal l T)
  D := fun T ↦ DerivedCategory.{u + 1} (modules l T)
  catC := fun _ ↦ inferInstance
  catD := fun _ ↦ inferInstance
  E := derivedEquivalence l
  P := internalPull l
  Q := nativePull l
  R := internalPush l
  S := nativePush l
  adjP := internalDerivedAdjunction l
  adjQ := nativeDerivedAdjunction l
  pc := internalPullComp l
  qc := nativePullComp l
  e := derivedPullComparison l
  m := fun f ↦ (Data.derivedPushComparison f).hom

/-- The derived mate and chain-map normalization for one scheme morphism.
Factoring this formula before field binders fixes its proof-valued site instances once.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Project, Tags 070Y and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev DerivedNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  (derivedComparisonFrame l).MateCondition f ∧
  ∀ (L : CochainComplex (modules l Y) ℤ)
    (I : CochainComplex (modules l X) ℤ) [I.IsKInjective]
    (a : ((inverse l f (d.coefficientMap f)).mapHomologicalComplex (.up ℤ)).obj L ⟶ I),
    (nativeDerivedAdjunction l f).homEquiv _ _
        ((inverse l f (d.coefficientMap f)).mapDerivedCategoryFactors.hom.app L ≫
          DerivedCategory.Q.map a) ≫
      ((direct l f (d.coefficientMap f)).rightDerivedFunctorObjQIso I).hom =
    DerivedCategory.Q.map
      (((adjunction l f (d.coefficientMap f)).mapHomologicalComplex (.up ℤ)
        ).homEquiv L I a)

/-- The exchange equation for one square and one derived object, without field binders.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Project, Tag 07A7.
(blueprint: def-sf-finite-span-module-comparison-data). -/
abbrev ExchangeEquation {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback g' f' f g)
    (K : (derivedComparisonFrame l).C X) : Prop :=
  (derivedComparisonFrame l).PullbackExchangeCondition s K

/-- The coefficient, ordinary, K-injective and derived normalizations, clause by clause.
The exact equivalence is the explicit scalar transport, and the comparisons below
are fixed by their section formulas, adjunction mates and right-derived units.
Source: Bhatt--Scholze 6.8.1--6.8.3 and 6.8.15; Stacks 03D7, 070Y and 09T5.
(blueprint: def-sf-finite-span-module-comparison-data). -/
def Properties : Prop :=
  -- chart
  (∀ (X : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField l)
    (V : X.ProEtᵒᵖ)
    (s : (condensedRingObj (Profinite.continuousMapRingObj E) X).obj.obj V)
    (x : V.unop.left),
    (((((upperStarFromPoint X).map (Profinite.padicSubfieldRingObjToPadicAlgCl l E) ≫
      (d.theta X).hom).hom.app V) s).down.1 x) =
        (((chartComparison X E).hom.app V s).down x : PadicAlgCl l)) ∧
  -- coefficient_sections
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEtᵒᵖ)
    (r : (ring l Y).obj.obj V) (x : ((InternalModuleOperations.siteMap f).obj V.unop).left),
    (((d.coefficientMap f).hom.app V r).down.1 x) =
      r.down.1 ((Limits.pullback.fst V.unop.hom f).base x)) ∧
  -- coefficient_square
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
      (lowerStar Ab.{u + 1} f).map (d.theta X).hom =
    (d.theta Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f)) ∧
  -- inverse_coefficient_square
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (upperStar Ab.{u + 1} f).map (d.theta Y).hom ≫ rho l f =
      condensedPullbackHom (Profinite.padicAlgClRingObj l) f ≫ (d.theta X).hom) ∧
  -- rho_invertible
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso (rho l f)) ∧
  -- rho_composition
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    rho l (f ≫ g) = (upperStarComp Ab.{u + 1} f g).hom.app (nativeAb l Z) ≫
      (upperStar Ab.{u + 1} f).map (rho l g) ≫ rho l f) ∧
  -- ordinary_mate
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (mateEquiv (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (adjunction l f (d.coefficientMap f)) (d.pullComparison f).inv).natTrans =
        (d.pushComparison f).hom) ∧
  -- push_identity
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : internal l X)
    (V : Y.ProEtᵒᵖ) (m : ((CondensedRing.lowerStar
      (Profinite.padicAlgClRingObj l) f).obj M).X.obj.obj V),
    (((d.pushComparison f).hom.app M).val.app V) m = m) ∧
  -- underlying
  (∀ X : Scheme.{u},
    (equivalence l X (d.theta X)).functor ⋙ SheafOfModules.toSheaf (ring l X) =
      Mod.forget (condensedRingObj (Profinite.padicAlgClRingObj l) X)) ∧
  -- finiteFree_sections
  (∀ (X : Scheme.{u}) (V : X.ProEtᵒᵖ) (M : internal l X) (n : ℕ)
    (b : Module.Basis (Fin n)
      ((InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) X).obj.obj V)
      (((InternalModuleOperations.equivalence
        (Profinite.padicAlgClRingObj l) X).functor.obj M).val.obj V)),
    ∃ b' : Module.Basis (Fin n) ((ring l X).obj.obj V)
      (((equivalence l X (d.theta X)).functor.obj M).val.obj V),
      ∀ i : Fin n, b' i = b i) ∧
  -- pushComposition_sections
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : modules l X) (V : Z.ProEtᵒᵖ)
    (m : ((direct l g (d.coefficientMap g)).obj
      ((direct l f (d.coefficientMap f)).obj M)).val.obj V),
    (((d.pushComposition f g).hom.app M).val.app V).hom m =
      (((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
        ((SheafOfModules.toSheaf (ring l X)).obj M)).hom.app V).hom m) ∧
  -- pullComposition_mate
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    d.pullComposition f g = (Adjunction.leftAdjointCompIso
      (adjunction l g (d.coefficientMap g)) (adjunction l f (d.coefficientMap f))
      (adjunction l (f ≫ g) (d.coefficientMap (f ≫ g))) (d.pushComposition f g)).symm) ∧
  -- ordinary_composition
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : internal l Z),
    (d.pullComparison (f ≫ g)).hom.app M ≫
      (d.pullComposition f g).hom.app ((equivalence l Z (d.theta Z)).functor.obj M) =
    (equivalence l X (d.theta X)).functor.map
      ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).hom.app M) ≫
      (d.pullComparison f).hom.app
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).obj M) ≫
      (inverse l f (d.coefficientMap f)).map ((d.pullComparison g).hom.app M)) ∧
  -- kinjective_forward
  (∀ (X : Scheme.{u}) (I : CochainComplex (internal l X) ℤ),
    I.IsKInjective → CochainComplex.IsKInjective
      (((equivalence l X (d.theta X)).functor.mapHomologicalComplex (.up ℤ)).obj I)) ∧
  -- kinjective_inverse
  (∀ (X : Scheme.{u}) (I : CochainComplex (modules l X) ℤ),
    I.IsKInjective → CochainComplex.IsKInjective
      (((equivalence l X (d.theta X)).inverse.mapHomologicalComplex (.up ℤ)).obj I)) ∧
  -- derived_push_normalization
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (internal l X) ℤ),
    (equivalence l Y (d.theta Y)).functor.mapDerivedCategory.map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctorUnitQ P) ≫
      (d.derivedPushComparison f).hom.app (DerivedCategory.Q.obj P) ≫
      (direct l f (d.coefficientMap f)).rightDerivedFunctor.map
        ((equivalence l X (d.theta X)).functor.mapDerivedCategoryFactors.hom.app P) =
    (equivalence l Y (d.theta Y)).functor.mapDerivedCategoryFactors.hom.app
      (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).mapHomologicalComplex
        (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (d.pushComparison f) (.up ℤ)).hom.app P) ≫
      (direct l f (d.coefficientMap f)).rightDerivedFunctorUnitQ
        (((equivalence l X (d.theta X)).functor.mapHomologicalComplex (.up ℤ)).obj P)) ∧
  -- field_normalization
  (∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    p ≠ l → ∀ (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y),
    DerivedNormalization l f.left)

/-- The normalized comparisons carry the specified exchange to the sectionwise counit mate.
Source: Stacks Project, Tag 07A7; Bhatt--Scholze, Remark 6.8.15.
(blueprint: def-sf-finite-span-module-comparison-data).

Proof: expand each mate by def-weil-pbc-adjunction-mate. The field_normalization equation
identifies the derived units and counits by transposition of identities, and
ordinary_composition localizes to identify the two inverse-image square maps.
Naturality of derivedPushComparison and derivedPullComparison identifies their
whiskerings. Compose these three equalities, cancel adjacent comparison inverses, and
obtain the displayed equality. This is step 8 of the node; no assertion that the exchange
is invertible is used, and no restriction is placed on the derived object K. -/
def ExchangeProperty : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (X' X Y' Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (s : IsPullback g'.left f'.left f.left g.left) (K : (derivedComparisonFrame l).C X.left),
    ExchangeEquation l s K

end AlgebraicGeometry.ProEtale.FiniteSpanComparison

