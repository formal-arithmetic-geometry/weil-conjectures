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
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorPresentation
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Compactification.Over
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-! # Compact projection formula for actual derived Weil complexes

Source: blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection (blueprint: lem-sf-derived-weil-compact-projection-formula).

The tensor and compact-support operations are the recorded native constructions.
The proper pullback/tensor comparison is pinned on sheaf summands and K-flat
representatives. The projection is pinned to the counit mate followed by the
normalized open comparison and the balanced pullback compositor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u a b

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- On each summand, totalized pullback/tensor is the specified sheaf comparison.
Using a generic exact functor keeps the comparison independent of any presentation
of the native fixed-pair functor.
Source: Stacks 07A4; blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-sf-derived-weil-compact-projection-formula). -/
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

/-- A presentation of balanced pullback/tensor, retaining its sheaf, total and
localized maps. The native compatibility conditions below pin every operation.
Source: Stacks 07A4, 0G7E; blueprint latest, fix-lem-tensor-adjunction.proof.md,
Step 1 (blueprint: lem-sf-derived-weil-compact-projection-formula). -/
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

/-- The balanced compositor for the specified compactification, in the direction
j* p* to f*. Source: fix-lem-tensor-adjunction.proof.md Step 1.
(blueprint: def-sf-native-projection-tensor-comparison-data). -/
abbrev nativeProjectionPullComp {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  (leftDerivedUpperStarCompactificationIso Λ c).symm

/-- The target of the compact projection formula, with the same ambient tensor and Rf!.
Source: fix-lem-tensor-adjunction.proof.md Step 1.
(blueprint: def-sf-native-projection-tensor-comparison-data). -/
abbrev nativeCompactProjectionRight {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  ((constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι.prod
    ((constantModelBoundedConstructible Λ Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙
      (upperStar Λ f).leftDerivedFunctor)) ⋙ Functor.uncurry.obj (derivedTensor Λ X) ⋙
        rightDerivedLowerShriekOfCompactification Λ c

/-- The source of the compact projection formula on finite-Tor constructible inputs,
viewed in the ambient ordinary derived category.
Source: fix-lem-tensor-adjunction.proof.md Step 1.
(blueprint: def-sf-native-projection-tensor-comparison-data). -/
abbrev nativeCompactProjectionLeft {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  (((constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙
      rightDerivedLowerShriekOfCompactification Λ c).prod
    (constantModelBoundedConstructible Λ Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι) ⋙
      Functor.uncurry.obj (derivedTensor Λ Y)

/-- The normalized counit mate is the library's canonical projection morphism.
Source: fix-lem-tensor-adjunction.proof.md Step 1, second Hom bijection.
(blueprint: def-sf-native-projection-tensor-comparison-data).
Proof: substitute the normalization of the tensor comparison. Both sides are the
same adjunction transpose of the pullback tensorator followed by counit tensor identity. -/
theorem nativeProjectionProperMate_eq (C : NativeProjectionTensorComparison Λ p)
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)))
    (T : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    nativeProjectionProperMate Λ p C A T = properProjectionMorphism Λ p A T := by
  unfold nativeProjectionProperMate
  rw [C.normalization]
  simp only [tensorHom_id]
  rfl

/-- The proper counit mate of the specified balanced tensor comparison.
No invertibility is part of this definition.
Source: fix-lem-tensor-adjunction.proof.md Step 1, second Hom bijection.
(blueprint: def-sf-native-projection-tensor-comparison-data). -/
def nativeProjectionProperMate (C : NativeProjectionTensorComparison Λ p)
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)))
    (T : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (lowerStar Λ p).rightDerivedFunctor.obj A ⊗ T ⟶
      (lowerStar Λ p).rightDerivedFunctor.obj
        (A ⊗ (upperStar Λ p).leftDerivedFunctor.obj T) :=
  (derivedUpperStarLowerStarAdjunction Λ p).homEquiv _ _
    ((C.mu.hom.app ((lowerStar Λ p).rightDerivedFunctor.obj A)).app T ≫
      ((derivedUpperStarLowerStarAdjunction Λ p).counit.app A ⊗ₘ 𝟙 _))

/-- The canonical comparison, without choosing any isomorphism from mere existence.
Source: the K-flat construction of the derived monoidal pullback.
(blueprint: def-sf-native-projection-tensor-comparison-data). -/
def nativeProjectionTensorComparison : NativeProjectionTensorComparison Λ p :=
  ⟨leftDerivedUpperStarTensorIso Λ p, rfl⟩

/-- The normalized comparison is the actual derived pullback tensor isomorphism.
Its construction in Derived.Monoidal fixes the ordinary balanced sheaf map, its
summand maps on total complexes, and its K-flat localization. No alternative tensorator
or projection-formula hypothesis is introduced.
Source: fix-lem-tensor-adjunction.proof.md Step 1, second Hom bijection.
(blueprint: def-sf-native-projection-tensor-comparison-data). -/
structure NativeProjectionTensorComparison where
  /-- The comparison on the two ambient ordinary derived categories. -/
  mu : leftDerivedUpperStarTensorLeft Λ p ≅ leftDerivedUpperStarTensorRight Λ p
  /-- Pinning to the canonical balanced, totalized and localized comparison. -/
  normalization : mu = leftDerivedUpperStarTensorIso Λ p

/-- Restriction of the ordinary condensed derived tensor to Dctf, with the same maps.
Source: fix-lem-tensor-adjunction.proof.md Step 1.
(blueprint: def-sf-native-constructible-tensor). -/
def nativeConstructibleTensor
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] :
    ConstantModelConstructibleFiniteTor Λ X × ConstantModelConstructibleFiniteTor Λ X ⥤
      ConstantModelConstructibleFiniteTor Λ X :=
  (constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _).lift
    (((constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι).prod
      ((constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _).ι) ⋙
        Functor.uncurry.obj (derivedTensor Λ X))
    (fun A ↦ nativeConstructibleTensor_mem Λ ell k hΛ X A.1 A.2)

/-- Tensor closure for the current finite-Tor constructible predicate.
Source: fix-lem-tensor-adjunction.proof.md Step 1, with tensor constructibility from
lem-sfb-admissible-tensor-constructibility.
(blueprint: def-sf-native-constructible-tensor).
Proof: apply admissible-coefficient constructibility to the two inputs. Choose their
Tor intervals [a,b] and [c,d]; the tensor has interval [a+c,b+d]. -/
theorem nativeConstructibleTensor_mem
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (A B : ConstantModelConstructibleFiniteTor Λ X) :
    (constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
      (((derivedTensor Λ X).obj A.obj).obj B.obj) := by
  refine ⟨constantModelBoundedConstructible_tensor_of_admissible
    ell k Λ hΛ A.obj B.obj A.property B.property, ?_⟩
  obtain ⟨a, b, hA⟩ := A.property.2
  obtain ⟨c, d, hB⟩ := B.property.2
  exact ⟨a + c, b + d, _root_.DerivedCategory.torAmplitudeIn_tensor hA hB⟩

end CategoryTheory

namespace AlgebraicGeometry

attribute [instance] Compactification.over

namespace WeilComplex

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The recorded native tensor restricted to its bounded constructible full subcategory.
Source: nativeDerivedTensor_mem_weilComplex; blueprint latest,
fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-sf-derived-weil-compact-projection-formula). -/
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

/-- Representative normalization for the proper factor's balanced tensor comparison.
This is data specifying the comparison, not a projection-formula assumption.
Sheaf maps are the existing balanced ordinary maps with their Weil structures;
total maps are fixed on every coproduct insertion; mu is their localization.
Source: Stacks 07A4, 0G7E; blueprint latest,
fix-lem-tensor-adjunction.proof.md, Step 1, second Hom bijection
(blueprint: lem-sf-derived-weil-compact-projection-formula). -/
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

/-- The proper projection mate of the actual derived counit and balanced comparison.
No invertibility is included in this definition.
Source: blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection (blueprint: lem-sf-derived-weil-compact-projection-formula). -/
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

/-- The framework's actual chosen compactification, with its canonical k0-structure.
Source: Nagata compactification over a field; blueprint latest,
fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-sf-derived-weil-compact-projection-formula). -/
abbrev nativeProjectionCompactification : Compactification f :=
  HasCompactification.compactification f
    (hf := HasCompactification.of_isOver (S := Spec (CommRingCat.of k₀)) f)

/-- Finite type of the chosen compactification source, by composition with its proper map.
Source: Stacks 01T3; node proof Step 1
(blueprint: lem-sf-derived-weil-compact-projection-formula).
Proof: the structure map is p followed by the finite-type structure map of Y;
proper maps are finite type, and finite-type maps compose. -/
instance nativeProjectionCompactification_locallyOfFiniteType :
    LocallyOfFiniteType ((nativeProjectionCompactification k₀ f).Z ↘
      Spec (CommRingCat.of k₀)) :=
  locallyOfFiniteType_comp (nativeProjectionCompactification k₀ f).g
    (Y ↘ Spec (CommRingCat.of k₀))

/-- Quasi-compactness of the chosen compactification source by proper composition.
Source: Stacks 01T3; node proof Step 1
(blueprint: lem-sf-derived-weil-compact-projection-formula).
Proof: p is proper, hence quasi-compact; compose with the quasi-compact map of Y. -/
instance nativeProjectionCompactification_quasiCompact :
    QuasiCompact ((nativeProjectionCompactification k₀ f).Z ↘
      Spec (CommRingCat.of k₀)) :=
  quasiCompact_comp (nativeProjectionCompactification k₀ f).g
    (Y ↘ Spec (CommRingCat.of k₀))

/-- Separatedness of the chosen compactification source by proper composition.
Source: Stacks 01KU; node proof Step 1
(blueprint: lem-sf-derived-weil-compact-projection-formula).
Proof: factor its diagonal through Z times_Y Z. The first map is closed since p
is proper, and the second is the pullback of the closed diagonal of Y. -/
instance nativeProjectionCompactification_isSeparated :
    IsSeparated ((nativeProjectionCompactification k₀ f).Z ↘
      Spec (CommRingCat.of k₀)) :=
  MorphismProperty.comp_mem (@IsSeparated) (nativeProjectionCompactification k₀ f).g
    (Y ↘ Spec (CommRingCat.of k₀)) inferInstance inferInstance

/-- The two-variable source of the compact projection formula.
Source: blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-sf-derived-weil-compact-projection-formula). -/
abbrev nativeCompactProjectionLeft :=
  (derivedLowerShriek k₀ l f).prod (𝟭 (WeilComplex k₀ l Y)) ⋙
    nativeConstructibleTensor k₀ l Y

/-- The two-variable target of the compact projection formula.
Source: blueprint latest, fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-sf-derived-weil-compact-projection-formula). -/
abbrev nativeCompactProjectionRight :=
  (𝟭 (WeilComplex k₀ l X)).prod (upperStar (k₀ := k₀) (l := l) f) ⋙
    nativeConstructibleTensor k₀ l X ⋙ derivedLowerShriek k₀ l f

/-- The balanced compositor for the actual chosen factorization of f.
Source: UpperStarComp.lean, UpperStarId.lean; blueprint latest,
fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-sf-derived-weil-compact-projection-formula). -/
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
