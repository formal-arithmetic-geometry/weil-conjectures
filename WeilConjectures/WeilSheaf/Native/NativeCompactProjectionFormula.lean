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
Source: native framework, LowerShriek.lean; blueprint latest,
fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-sf-derived-weil-compact-projection-formula). -/
abbrev nativeProjectionCompactification : Compactification f :=
  HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)

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
