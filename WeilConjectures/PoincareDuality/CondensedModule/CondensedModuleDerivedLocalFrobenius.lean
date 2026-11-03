/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport

/-! # Native derived condensed local Frobenius

Source: latest blueprint, def-weil-local-frobenius-trace, closed-point return construction
(blueprint: def-weil-local-frobenius-trace).

The degree-zero module operator remains available from its separate module. This file supplies
the corresponding construction on strict derived pairs, with no finite-stage choice.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace WeilConjectures.CondensedModule
open CondensedRing.CohomologyTransport

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Iterate the native derived Weil map with its specified pullback compositors.
The positive-power index n means exponent n+1, as for the imported module operator.
Source: latest blueprint, local-return construction
(blueprint: def-weil-local-frobenius-trace). -/
def derivedIterate {T : Scheme.{u}} (g : T ⟶ T)
    (M : CondensedRing.CohomologyTransport.D Λ T)
    (φ : (L Λ g).obj M ≅ M) :
    (n : ℕ) → (L Λ
      (localPositivePower g n)).obj M ≅ M
  | 0 => φ
  | n + 1 =>
    (CondensedRing.leftDerivedUpperStarComp Λ
      (localPositivePower g n) g).app M ≪≫
      (L Λ
        (localPositivePower g n)).mapIso φ ≪≫ derivedIterate g M φ n

/-- The native derived closed-point operator: terminal reparametrization, return
comparison, and the iterated Weil map, in that order. Taking H^j is the local operator
on stalk cohomology, because the module inverse image and point sections are exact.
Source: Deligne, Weil II (1.1.7)--(1.1.10); latest blueprint local-return convention
(blueprint: def-weil-local-frobenius-trace). -/
def derivedOperator (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (g : T ⟶ T)
    (M : CondensedRing.CohomologyTransport.D Λ T)
    (φ : (L Λ g).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    End ((Γ Λ (Spec (.of D.k))).obj ((L Λ z).obj M)) :=
  End.of ((insertion Λ
      (localPositivePower (frobeniusPointIso D).hom n)).hom.app
        ((L Λ z).obj M) ≫
    (Γ Λ (Spec (.of D.k))).map
      ((CondensedRing.pullbackSquareComparison Λ
        (CommSq.mk h.symm)).inv.app M ≫
        (L Λ z).map (derivedIterate Λ g M φ n).hom))

/-- The ordinary scalar cohomology functor in an integer degree.
Source: latest blueprint, stalk cohomology clause
(blueprint: def-weil-local-frobenius-trace). -/
abbrev derivedScalarCohomology (j : ℤ) :=
  @DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2}
    (ModuleCat.{u + 1, u + 1} (condensedScalarRing Λ)) inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian
      (ModuleCat.{u + 1, u + 1} (condensedScalarRing Λ))) j

/-- The local operator on the cohomology stalk in degree j.
Source: latest blueprint, F_x^(n) on H^j, with exact point sections
(blueprint: def-weil-local-frobenius-trace). -/
def derivedCohomologyOperator (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (g : T ⟶ T)
    (M : CondensedRing.CohomologyTransport.D Λ T)
    (φ : (L Λ g).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) (j : ℤ) :=
  (derivedScalarCohomology Λ j).map (derivedOperator Λ D g M φ z n h)

/-- The alternating ordinary linear trace of the local derived operator.
For the bounded constructible field-coefficient objects in the node, the displayed
finsum has finite support. The sign j.negOnePow also covers negative degrees.
Source: latest blueprint, local alternating trace display
(blueprint: def-weil-local-frobenius-trace). -/
def derivedAlternatingTrace (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (g : T ⟶ T)
    (M : CondensedRing.CohomologyTransport.D Λ T)
    (φ : (L Λ g).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) : condensedScalarRing Λ :=
  ∑ᶠ j : ℤ, (j.negOnePow : ℤ) •
    LinearMap.trace (condensedScalarRing Λ)
      ((derivedScalarCohomology Λ j).obj ((Γ Λ (Spec (.of D.k))).obj ((L Λ z).obj M)))
      (derivedCohomologyOperator Λ D g M φ z n h j).hom

end WeilConjectures.CondensedModule
