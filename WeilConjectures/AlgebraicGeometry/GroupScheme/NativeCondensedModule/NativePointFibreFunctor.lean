/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius

/-! # The native point-fibre functor

Point pullback followed by native sections, with its object expressed as the
existing native fibre. Source: latest blueprint, finite geometric evaluation
(blueprint: def-a1-native-point-fibre-functor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeCondensedModule

/-- Functorial sections of point pullback, with the existing native fibre as its object.
Source: latest blueprint, finite evaluation display and its naturality
(blueprint: def-a1-native-point-fibre-functor). -/
def pointFibreFunctor (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) :
    Modules l T ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)) where
  obj M := fibre l D M z
  map f := (pointSections l D.k).map
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f)
  map_id M := ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z) ⋙
    pointSections l D.k).map_id M
  map_comp f g := ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z) ⋙
    pointSections l D.k).map_comp f g

/-- The fibre functor has the specified native fibre as its object, without transport.
Source: latest blueprint, the vector space F_z
(blueprint: def-a1-native-point-fibre-functor). -/
theorem pointFibreFunctor_obj (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (M : Modules l T) :
    (pointFibreFunctor l D z).obj M = fibre l D M z := rfl

/-- The native fibre functor is point pullback followed by actual point sections.
Source: latest blueprint, natural evaluation
(blueprint: def-a1-native-point-fibre-functor). -/
theorem pointFibreFunctor_eq (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) :
    pointFibreFunctor l D z =
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙ pointSections l D.k := rfl

end WeilConjectures.NativeCondensedModule
