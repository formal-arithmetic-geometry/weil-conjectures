/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Fixed data for native derived restriction

Source: blueprint derived pullback; Stacks Project, Tag 08JB.
The functor and its native strong monoidal structure are constructed together, so
later comparisons share their auxiliary tensor instances.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [instance 50000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u a b c d
open CategoryTheory WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A functor together with its specified strong monoidal structure.
Source: Stacks 06YU (blueprint: def-sfb-native-derived-restriction-data). -/
structure NativeMonoidalData (C : Type a) [Category.{b} C] [MonoidalCategory C]
    (D : Type c) [Category.{d} D] [MonoidalCategory D] where
  functor : C ⥤ D
  monoidal : functor.Monoidal

/-- Package an already specified monoidal functor, without changing its data.
Source: Stacks 06YU (blueprint: def-sfb-native-derived-restriction-data). -/
def dataOfMonoidal {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    {F : C ⥤ D} (m : F.Monoidal) : NativeMonoidalData C D := ⟨F, m⟩

/-- The existing native K-flat restriction and exactly its canonical monoidal instance.
This is a concrete construction from `monoidal_leftDerivedUpperStar`, with no choice
of a witness from an existence theorem.
Source: blueprint derived pullback; Stacks 08JB
(blueprint: def-sfb-native-derived-restriction-data). -/
def nativeDerivedRestrictionData
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    NativeMonoidalData (DerivedCategory (Internal Λ.X X))
      (DerivedCategory (Internal Λ.X Y)) :=
  dataOfMonoidal (monoidal_leftDerivedUpperStar Λ.X f)

/-- The packaged functor has the canonical exact-pullback isomorphism criterion.
Source: Stacks 08JB (blueprint: def-sfb-native-derived-restriction-data).
Proof: use the existing natural isomorphism from native left-derived pullback to
exact termwise derived pullback; natural isomorphisms conjugate mapped morphisms. -/
theorem nativeDerivedRestriction_isIso_map_iff
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {K N : DerivedCategory (Internal Λ.X X)} (g : K ⟶ N) :
    IsIso ((nativeDerivedRestrictionData Λ f).functor.map g) ↔
      IsIso ((upperStar Λ.X f).mapDerivedCategory.map g) := by
  exact NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f) g

end AlgebraicGeometry.ProEtale.CondensedRing
