/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenScalarTensorNativeModels
public import WeilConjectures.SixFunctors.OpenScalarOrdinaryMonoidal
public import WeilConjectures.SixFunctors.OpenScalarDerivedMonoidal

/-! # A constructed native monoidal inverse image

Source: Stacks Project, Tags 03EL, 07A4 and 0FPT.
(blueprint: lem-sp-open-scalar-native-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- Transport a strong monoidal functor along equal monoidal structures.
Source: equality elimination (blueprint: lem-sp-open-scalar-native-pullback). -/
@[instance_reducible]
def transportMonoidal {C D : Type*} [Category* C] [Category* D]
    {s s' : MonoidalCategory C} {t t' : MonoidalCategory D}
    (hs : s = s') (ht : t = t') (F : C ⥤ D)
    (n : @Functor.Monoidal C _ s' D _ t' F) :
    @Functor.Monoidal C _ s D _ t F := by
  cases hs
  cases ht
  exact n

/-- The transported tensorator is heterogeneously equal to the original one.
Source: equality elimination (blueprint: lem-sp-open-scalar-native-pullback).
Proof: eliminate both structure equalities; the assertion is then reflexivity. -/
theorem transportMonoidal_delta {C D : Type*} [Category* C] [Category* D]
    {s s' : MonoidalCategory C} {t t' : MonoidalCategory D}
    (hs : s = s') (ht : t = t') (F : C ⥤ D)
    (n : @Functor.Monoidal C _ s' D _ t' F) (K L : C) :
    HEq (@Functor.OplaxMonoidal.δ C _ s D _ t F
      (transportMonoidal hs ht F n).toOplaxMonoidal K L)
      (@Functor.OplaxMonoidal.δ C _ s' D _ t' F n.toOplaxMonoidal K L) := by
  cases hs
  cases ht
  rfl

/-- The monoidal structure obtained by deriving the normalized ordinary inverse image.
Source: Stacks Project, Tags 03EL, 07A4 and 0FPT
(blueprint: lem-sp-open-scalar-native-pullback). -/
@[instance_reducible]
def nativePullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    letI := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology Y) R
    letI := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology X) S
    (proEtaleRingDerivedPullback f R S c).Monoidal :=
  (derived_monoidal f R S c (ordinary_monoidal f R S c).choose).choose

/-- The constructed native pullback structure in the selected model presentations.
Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-sp-open-scalar-native-pullback).

Construction: first use the proved ordinary tensor and unit comparison to construct
the strong ordinary pullback. Derive it by the proved exact flat-preserving monoidal
construction. Finally transport source and target monoidal structures through the
recorded native equalities. No existence theorem with a postponed proof supplies data. -/
@[instance_reducible]
def nativeOpenMonoidal (m : Models.{u}) (hm : NativeModels m)
    (A : Type u) [CommRing A] {U X : Scheme.{u}} (j : U ⟶ X) :
    OpenMonoidal m A j :=
  transportMonoidal (hm X (proEtaleConstantRing X A)).1
    (hm U (proEtaleConstantRing U A)).1 (constantPullback (A := A) j)
    (nativePullbackMonoidal j (proEtaleConstantRing X A) (proEtaleConstantRing U A)
      (proEtaleConstantRingComparison j A))

/-- The selected-model tensorator is the transport of the native derived tensorator.
Source: Stacks Project, Tag 0FPT
(blueprint: lem-sp-open-scalar-native-pullback).
Proof: apply the equality-elimination formula for transporting monoidal functors. -/
theorem nativeOpenMonoidal_delta (m : Models.{u}) (hm : NativeModels m)
    (A : Type u) [CommRing A] {U X : Scheme.{u}} (j : U ⟶ X)
    (F G : proEtaleDerivedCategory X A) :
    letI := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology X) (proEtaleConstantRing X A)
    letI := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology U) (proEtaleConstantRing U A)
    letI : (constantPullback (A := A) j).Monoidal :=
      nativePullbackMonoidal j (proEtaleConstantRing X A) (proEtaleConstantRing U A)
        (proEtaleConstantRingComparison j A)
    HEq (openDelta m A j (nativeOpenMonoidal m hm A j) F G)
      (Functor.OplaxMonoidal.δ (constantPullback (A := A) j) F G) := by
  exact transportMonoidal_delta (hm X (proEtaleConstantRing X A)).1
    (hm U (proEtaleConstantRing U A)).1 (constantPullback (A := A) j)
    (nativePullbackMonoidal j (proEtaleConstantRing X A) (proEtaleConstantRing U A)
      (proEtaleConstantRingComparison j A)) F G

end AlgebraicGeometry.ProEtale.OpenScalarTensor
