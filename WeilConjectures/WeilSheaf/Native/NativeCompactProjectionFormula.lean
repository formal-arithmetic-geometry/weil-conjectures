/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.UpperStarId
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.Native.NativeDerivedWeilTensorConstructible
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenDerivedTensor
import WeilConjectures.AlgebraicGeometry.Native.NativeBasicComparisons
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Compact projection formula for actual derived Weil complexes

This file sets up the ingredients of the compact projection formula
`f_! A ⊗ T ≅ f_! (A ⊗ f^* T)` for derived Weil complexes: the constructible tensor, the
balanced pullback/tensor comparison for the proper factor, its projection mate, and the
chosen compactification of `f`.

## Implementation details

The tensor and compact-support operations are the recorded native constructions.
The proper pullback/tensor comparison is pinned on sheaf summands and K-flat
representatives, using a generic exact functor so that it is independent of any
presentation of the native fixed-pair functor. The projection is pinned to the counit
mate followed by the normalized open comparison and the balanced pullback compositor.

## References

* [Stacks, Tags 07A4, 0G7E, 01T3, 01KU]
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u a b

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- On each summand, the totalized pullback/tensor comparison is the specified sheaf
comparison. -/
def ProjectionTensorSummandNormalization
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] (SA : A × A ⥤ A) (SB : B × B ⥤ B)
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (iA : ∀ P T (a b n : ℤ), a + b = n →
      (SA.obj (P.X a, T.X b) ⟶ ((TA.obj P).obj T).X n))
    (iB : ∀ P T (a b n : ℤ), a + b = n →
      (SB.obj (P.X a, T.X b) ⟶ ((TB.obj P).obj T).X n))
    (sheaf : ∀ M N, F.obj (SA.obj (M, N)) ≅ SB.obj (F.obj M, F.obj N))
    (total : ∀ P T, (F.mapHomologicalComplex (.up ℤ)).obj ((TA.obj P).obj T) ≅
      (TB.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj T)) : Prop :=
  ∀ P T (a b n : ℤ) (h : a + b = n),
    F.map (iA P T a b n h) ≫ (total P T).hom.f n =
      (sheaf (P.X a) (T.X b)).hom ≫
        iB ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj T) a b n h

/-- A presentation of the balanced pullback/tensor comparison, retaining its sheaf, total
and localized maps. -/
structure ProjectionTensorPresentation
    (A B : Type a) [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B] where
  /-- Actual pullback on sheaves. -/
  F : A ⥤ B
  /-- Additivity. -/
  [add : F.Additive]
  /-- Left exactness. -/
  [lim : PreservesFiniteLimits F]
  /-- Right exactness. -/
  [colim : PreservesFiniteColimits F]
  /-- Source tensor on sheaves. -/
  SA : A × A ⥤ A
  /-- Target tensor on sheaves. -/
  SB : B × B ⥤ B
  /-- Source total tensor. -/
  TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ
  /-- Target total tensor. -/
  TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ
  /-- Source derived tensor. -/
  DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A
  /-- Target derived tensor. -/
  DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B
  /-- Source K-flatness. -/
  flatA : CochainComplex A ℤ → Prop
  /-- Target K-flatness. -/
  flatB : CochainComplex B ℤ → Prop
  /-- Preservation of K-flat representatives. -/
  kflat : ∀ P, flatA P → flatB ((F.mapHomologicalComplex (.up ℤ)).obj P)
  /-- Source representative model. -/
  modelA : ∀ P T, flatA P → flatA T →
    (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((TA.obj P).obj T))
  /-- Target representative model. -/
  modelB : ∀ P T, flatB P → flatB T →
    (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj ((TB.obj P).obj T))
  /-- Source summand insertion. -/
  iA : ∀ P T (a b n : ℤ), a + b = n →
    (SA.obj (P.X a, T.X b) ⟶ ((TA.obj P).obj T).X n)
  /-- Target summand insertion. -/
  iB : ∀ P T (a b n : ℤ), a + b = n →
    (SB.obj (P.X a, T.X b) ⟶ ((TB.obj P).obj T).X n)
  /-- Balanced sheaf comparison. -/
  sheaf : ∀ M N, F.obj (SA.obj (M, N)) ≅ SB.obj (F.obj M, F.obj N)
  /-- Its totalization. -/
  total : ∀ P T, (F.mapHomologicalComplex (.up ℤ)).obj ((TA.obj P).obj T) ≅
    (TB.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj T)
  /-- Equality on each summand, fixing the chain map. -/
  summands : ProjectionTensorSummandNormalization F SA SB TA TB iA iB sheaf total
  /-- The derived balanced comparison. -/
  mu : DA ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory.prod F.mapDerivedCategory ⋙ DB
  /-- It localizes precisely the total map on arbitrary K-flat inputs. -/
  models : OpenTensorRestrictionNormalization F TB TA DB DA flatB flatA kflat
    modelB modelA total mu

end CategoryTheory

namespace AlgebraicGeometry

attribute [instance] Compactification.over

namespace WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The native derived tensor restricted to the bounded constructible full subcategory. -/
def nativeConstructibleTensor (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    WeilComplex k₀ l X × WeilComplex k₀ l X ⥤ WeilComplex k₀ l X :=
  (objectProperty k₀ l X).lift
    ((objectProperty k₀ l X).ι.prod (objectProperty k₀ l X).ι ⋙
      ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X)
    (fun A ↦ nativeDerivedTensor_mem_weilComplex k₀ l X A.2 A.1)

end WeilComplex

namespace ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

/-- The balanced pullback/tensor comparison along the proper map `p`, together with a
representative presentation whose sheaf maps are the balanced module comparisons, whose
total maps are fixed on each coproduct insertion, and whose derived map `mu` is their
localization. -/
structure NativeProjectionTensorComparison where
  /-- Natural balanced comparison in the actual ambient derived category. -/
  mu : nativeDerivedTensor k₀ l Y ⋙ nativeOpenPull k₀ l p ≅
    (nativeOpenPull k₀ l p).prod (nativeOpenPull k₀ l p) ⋙ nativeDerivedTensor k₀ l Z
  /-- Representative presentation, retaining all chain and localization equations. -/
  presentation : ProjectionTensorPresentation
    (ProEtaleWeilSheaf k₀ l Y) (ProEtaleWeilSheaf k₀ l Z)
  /-- All operations and comparison maps are exactly the native ones. -/
  compatibility : HEq presentation.F (upperStar k₀ l p) ∧
    HEq presentation.SA (nativeOpenSheafTensor k₀ l Y) ∧
    HEq presentation.SB (nativeOpenSheafTensor k₀ l Z) ∧
    HEq presentation.TA (nativeTensorTotal k₀ l Y) ∧
    HEq presentation.TB (nativeTensorTotal k₀ l Z) ∧
    HEq presentation.DA (nativeDerivedTensor k₀ l Y) ∧
    HEq presentation.DB (nativeDerivedTensor k₀ l Z) ∧
    HEq presentation.flatA (NativeIsKFlat k₀ l Y) ∧
    HEq presentation.flatB (NativeIsKFlat k₀ l Z) ∧
    HEq presentation.modelA (nativeOpenTensorModel k₀ l Y) ∧
    HEq presentation.modelB (nativeOpenTensorModel k₀ l Z) ∧
    HEq presentation.iA (nativeOpenTensorInsertion k₀ l Y) ∧
    HEq presentation.iB (nativeOpenTensorInsertion k₀ l Z) ∧
    HEq presentation.mu mu
  /-- Its sheaf map is the existing balanced module comparison, after forgetting. -/
  sheaf_forget : ∀ M N, HEq (presentation.sheaf M N).hom.hom.f
    ((ProEtale.adicUpperStarTensorLeftIso l
      (Scheme.Hom.geometricFiberMap p (comp_over p _)) N.carrier).hom.app M.carrier)

/-- The projection map `p_* A ⊗ T ⟶ p_* (A ⊗ p^* T)`, the mate of the derived counit
composed with the balanced comparison. -/
def nativeProjectionProperMate (C : NativeProjectionTensorComparison k₀ l p)
    (A : DerivedCategory (ProEtaleWeilSheaf k₀ l Z))
    (T : DerivedCategory (ProEtaleWeilSheaf k₀ l Y)) :
    (nativeDerivedTensor k₀ l Y).obj ((lowerStar k₀ l p).rightDerivedFunctor.obj A, T) ⟶
      (lowerStar k₀ l p).rightDerivedFunctor.obj
        ((nativeDerivedTensor k₀ l Z).obj (A, (nativeOpenPull k₀ l p).obj T)) :=
  (derivedUpperStarLowerStarAdjunction k₀ l p).homEquiv _ _
    (C.mu.hom.app ((lowerStar k₀ l p).rightDerivedFunctor.obj A, T) ≫
      (nativeDerivedTensor k₀ l Z).map
        (Prod.mkHom ((derivedUpperStarLowerStarAdjunction k₀ l p).counit.app A) (𝟙 _)))

end ProEtaleWeilSheaf

namespace WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The chosen compactification of `f`, with its canonical `k₀`-structure. -/
abbrev nativeProjectionCompactification : Compactification f :=
  HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)

/-- The source of the chosen compactification is locally of finite type over `k₀`. -/
instance nativeProjectionCompactification_locallyOfFiniteType :
    LocallyOfFiniteType ((nativeProjectionCompactification k₀ f).Z ↘
      Spec (CommRingCat.of k₀)) :=
  locallyOfFiniteType_comp (nativeProjectionCompactification k₀ f).g
    (Y ↘ Spec (CommRingCat.of k₀))

/-- The source of the chosen compactification is quasi-compact over `k₀`. -/
instance nativeProjectionCompactification_quasiCompact :
    QuasiCompact ((nativeProjectionCompactification k₀ f).Z ↘
      Spec (CommRingCat.of k₀)) :=
  quasiCompact_comp (nativeProjectionCompactification k₀ f).g
    (Y ↘ Spec (CommRingCat.of k₀))

/-- The source of the chosen compactification is separated over `k₀`. -/
instance nativeProjectionCompactification_isSeparated :
    IsSeparated ((nativeProjectionCompactification k₀ f).Z ↘
      Spec (CommRingCat.of k₀)) :=
  MorphismProperty.comp_mem (@IsSeparated) (nativeProjectionCompactification k₀ f).g
    (Y ↘ Spec (CommRingCat.of k₀)) inferInstance inferInstance

/-- The two-variable source `(A, T) ↦ f_! A ⊗ T` of the compact projection formula. -/
abbrev nativeCompactProjectionLeft :=
  (derivedLowerShriek k₀ l f).prod (𝟭 (WeilComplex k₀ l Y)) ⋙
    nativeConstructibleTensor k₀ l Y

/-- The two-variable target `(A, T) ↦ f_! (A ⊗ f^* T)` of the compact projection formula. -/
abbrev nativeCompactProjectionRight :=
  (𝟭 (WeilComplex k₀ l X)).prod (upperStar (k₀ := k₀) (l := l) f) ⋙
    nativeConstructibleTensor k₀ l X ⋙ derivedLowerShriek k₀ l f

/-- The pullback compositor `i^* ∘ g^* ≅ f^*` for the chosen compactification `f = g ∘ i`. -/
def nativeProjectionPullComp :
    ProEtaleWeilSheaf.nativeOpenPull k₀ l (nativeProjectionCompactification k₀ f).g ⋙
        ProEtaleWeilSheaf.nativeOpenPull k₀ l (nativeProjectionCompactification k₀ f).i ≅
      (ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory :=
  ProEtaleWeilSheaf.nativeOpenPullComp k₀ l
      (nativeProjectionCompactification k₀ f).i (nativeProjectionCompactification k₀ f).g ≪≫
    Functor.mapDerivedCategoryNatIso (ProEtaleWeilSheaf.upperStarCongrIso k₀ l
      (nativeProjectionCompactification k₀ f).comm.symm)

end WeilComplex
end AlgebraicGeometry
