/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod

/-! # Condensed local return operators without coefficient presentations

Source: latest blueprint, `def-weil-local-frobenius-trace`, the semilinear return
and the ordinary scalar stalk convention (blueprint: def-weil-local-frobenius-trace).

These maps use the actual condensed module pullback, its specified composition
isomorphism, and the canonical point trivialization. Powers are ordinary endomorphism
powers, with exponent n. The construction is valid before imposing constructibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedReturn
open CondensedRing.CohomologyTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Ordinary scalar cohomology, with the published derived-category universe.
Source: cohomology stalk convention (blueprint: def-weil-local-frobenius-trace). -/
abbrev scalarCohomology (j : ℤ) :=
  @DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2}
    (ModuleCat.{u + 1, u + 1} (condensedScalarRing Λ)) inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian
      (ModuleCat.{u + 1, u + 1} (condensedScalarRing Λ))) j

/-- Iterate the derived Weil map with the canonical pullback unit and compositors.
Source: the iterated Weil structure (blueprint: def-weil-local-frobenius-trace). -/
def derivedIterate {T : Scheme.{u}} (g : End T) (K : D Λ T)
    (φ : (L Λ g).obj K ≅ K) : (n : ℕ) → (L Λ (g ^ n)).obj K ≅ K
  | 0 => (CondensedRing.leftDerivedUpperStarId Λ T).app K
  | n + 1 =>
    eqToIso (congrArg (fun f ↦ (L Λ f).obj K) (pow_succ' g n)) ≪≫
      (CondensedRing.leftDerivedUpperStarComp Λ (g ^ n) g).app K ≪≫
      (L Λ (g ^ n)).mapIso φ ≪≫ derivedIterate g K φ n

/-- The local return: inverse point trivialization, the semilinear pullback square,
and the iterated Weil map, evaluated on point sections.
Source: local Frobenius recipe (blueprint: def-weil-local-frobenius-trace). -/
def derivedOperator {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (g : End T) (b : End (Spec (.of k)))
    (K : D Λ T) (φ : (L Λ g).obj K ≅ K) (z : Spec (.of k) ⟶ T) (n : ℕ)
    (h : z ≫ (g ^ n) = (b ^ n) ≫ z) :
    End ((Γ Λ (Spec (.of k))).obj ((L Λ z).obj K)) :=
  (insertion Λ (b ^ n)).hom.app ((L Λ z).obj K) ≫
    (Γ Λ (Spec (.of k))).map
      (((CondensedRing.leftDerivedUpperStarComp Λ (b ^ n) z).inv.app K) ≫
        eqToHom (congrArg (fun f ↦ (L Λ f).obj K) h.symm) ≫
        (CondensedRing.leftDerivedUpperStarComp Λ z (g ^ n)).hom.app K ≫
        (L Λ z).map (derivedIterate Λ g K φ n).hom)

/-- The ordinary linear local operator on cohomology of the derived fibre.
Source: F_x^(n) on cohomology (blueprint: def-weil-local-frobenius-trace). -/
def cohomologyOperator {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (g : End T) (b : End (Spec (.of k)))
    (K : D Λ T) (φ : (L Λ g).obj K ≅ K) (z : Spec (.of k) ⟶ T) (n : ℕ)
    (h : z ≫ (g ^ n) = (b ^ n) ≫ z) (j : ℤ) :=
  (scalarCohomology Λ j).map (derivedOperator Λ g b K φ z n h)

/-- Categorical recursion using a fixed unit and the specified pullback compositors.
This helper keeps recursion separate from the concrete module-object implementation.
Source: iteration of the Weil structure (blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def iterateFromCompositors {C : Type v} [Category.{w} C]
    (P : C ⥤ C) (F : ℕ → C ⥤ C) (unitComparison : F 0 ≅ 𝟭 C)
    (step : ∀ n : ℕ, F (n + 1) ≅ P ⋙ F n) (M : C) (φ : P.obj M ≅ M) :
    (n : ℕ) → (F n).obj M ≅ M :=
  Nat.rec (motive := fun n ↦ (F n).obj M ≅ M) (unitComparison.app M)
    (fun n previous ↦ (step n).app M ≪≫ (F n).mapIso φ ≪≫ previous)

/-- Iterate the Weil-module map with precisely the module pullback compositors.
Source: the degree-zero local recipe (blueprint: def-weil-local-frobenius-trace). -/
@[irreducible] def moduleIterate {T : Scheme.{u}} (g : End T)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (φ : (CondensedRing.upperStar Λ g).obj M ≅ M) :
    (n : ℕ) → (CondensedRing.upperStar Λ (g ^ n)).obj M ≅ M :=
  iterateFromCompositors (CondensedRing.upperStar Λ g)
    (fun n ↦ CondensedRing.upperStar Λ (g ^ n))
    (CondensedRing.upperStarEqToIso Λ (pow_zero g) ≪≫ CondensedRing.upperStarId Λ T)
    (fun n ↦ CondensedRing.upperStarEqToIso Λ (pow_succ' g n) ≪≫
      CondensedRing.upperStarComp Λ (g ^ n) g) M φ

/-- Local return on an actual module fibre, with inverse point trivialization.
Source: the operator on a cohomology sheaf (blueprint: def-weil-local-frobenius-trace). -/
def moduleOperator {k : Type u} [Field k] [IsAlgClosed k]
    {T : Scheme.{u}} (g : End T) (b : End (Spec (.of k)))
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (φ : (CondensedRing.upperStar Λ g).obj M ≅ M) (z : Spec (.of k) ⟶ T) (n : ℕ)
    (h : z ≫ (g ^ n) = (b ^ n) ≫ z) :
    End ((sections Λ (Spec (.of k))).obj ((CondensedRing.upperStar Λ z).obj M)) :=
  (sections Λ (Spec (.of k))).map
    ((CondensedRing.upperStarIsoIdOfIsSepClosed Λ (b ^ n)).inv.app
        ((CondensedRing.upperStar Λ z).obj M) ≫
      (CondensedRing.upperStarComp Λ (b ^ n) z).inv.app M ≫
      eqToHom (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj M) h.symm) ≫
      (CondensedRing.upperStarComp Λ z (g ^ n)).hom.app M ≫
      (CondensedRing.upperStar Λ z).map (moduleIterate Λ g M φ n).hom)

end WeilConjectures.CondensedReturn
