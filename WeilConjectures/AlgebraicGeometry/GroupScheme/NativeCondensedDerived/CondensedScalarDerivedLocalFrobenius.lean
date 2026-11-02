/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPoint.NativeCondensedPointSections
public import Mathlib.LinearAlgebra.Trace

/-! # Native derived local Frobenius with ordinary scalar stalks

Source: latest blueprint, def-weil-local-frobenius-trace, the local-return and
ordinary scalar stalk paragraphs (blueprint: def-weil-local-frobenius-trace).

All derived functors here are localizations of the exact functors applied termwise.
The construction works for every commutative condensed ring, hence both coefficient fields.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeCondensedDerived
open NativeCondensedModule

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ordinary unbounded derived category of actual coefficient modules.
Source: latest blueprint, K in Dbc (blueprint: def-weil-local-frobenius-trace). -/
abbrev Ambient (T : Scheme.{u}) := DerivedCategory (NativeCondensedPoint.Modules Λ T)

/-- Exact pullback localized termwise; it is the canonical Lf* for these coefficients.
Source: latest blueprint, exact condensed pullback (blueprint: def-weil-local-frobenius-trace). -/
abbrev pull {T U : Scheme.{u}} (f : T ⟶ U) := (CondensedRing.upperStar Λ f).mapDerivedCategory

/-- The ordinary scalar stalk complex is exact point sections after exact pullback.
Source: latest blueprint, scalar stalk convention (blueprint: def-weil-local-frobenius-trace). -/
abbrev stalk (D : FiniteFieldDatum.{u}) {T : Scheme.{u}} (M : Ambient Λ T)
    (z : Spec (.of D.k) ⟶ T) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (NativeCondensedPoint.sections Λ D.k).mapDerivedCategory.obj ((pull Λ z).obj M)

/-- Iterate the Weil isomorphism with the localized exact pullback compositor.
Source: latest blueprint, theta^[n] (blueprint: def-weil-local-frobenius-trace). -/
def iterate {T : Scheme.{u}} (g : T ⟶ T) (M : Ambient Λ T)
    (θ : (pull Λ g).obj M ≅ M) :
    (n : ℕ) → (pull Λ (localPositivePower g n)).obj M ≅ M
  | 0 => θ
  | n + 1 =>
    (Functor.mapDerivedCategoryNatIso
      (CondensedRing.upperStarComp Λ (localPositivePower g n) g)).app M ≪≫
    (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ g)
      (CondensedRing.upperStar Λ (localPositivePower g n))).app M ≪≫
    (pull Λ (localPositivePower g n)).mapIso θ ≪≫ iterate g M θ n

/-- Local return operator: source reparametrization, canonical pullback comparison,
then the iterated Weil isomorphism, localized to the ordinary scalar derived stalk.
Source: latest blueprint, semilinear return (blueprint: def-weil-local-frobenius-trace). -/
def operator (D : FiniteFieldDatum.{u}) {T : Scheme.{u}} (g : T ⟶ T)
    (M : Ambient Λ T) (θ : (pull Λ g).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) : End (stalk Λ D M z) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (NativeCondensedPoint.sections Λ D.k).mapDerivedCategory.map
    ((Functor.mapDerivedCategoryNatIso
      ((Functor.rightUnitor (CondensedRing.upperStar Λ z)).symm ≪≫
        CondensedRing.pointComparison Λ
          (CondensedRing.upperStarIsoIdOfIsSepClosed Λ
            (localPositivePower (frobeniusPointIso D).hom n))
          (localPositivePower g n) h)).hom.app M ≫
      (Functor.mapDerivedCategoryCompIso
        (CondensedRing.upperStar Λ (localPositivePower g n))
        (CondensedRing.upperStar Λ z)).hom.app M ≫
      (pull Λ z).map (iterate Λ g M θ n).hom)

/-- Ordinary scalar cohomology in an arbitrary integer degree.
Source: latest blueprint, H^j of the stalk (blueprint: def-weil-local-frobenius-trace). -/
abbrev cohomology (j : ℤ) :=
  DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) j

end WeilConjectures.NativeCondensedDerived
