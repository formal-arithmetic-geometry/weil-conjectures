/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.CondensedPointModuleComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.BigOperators.Finprod

import WeilConjectures.AlgebraicGeometry.CondensedPointCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.CondensedFibreComparisonCoherence
import WeilConjectures.SixFunctors.ScalarSixPullback

/-! # Native condensed local Frobenius in degree zero

Source: latest blueprint, def-weil-local-frobenius-trace, geometric-point return convention
(blueprint: lem-zl-constant-stalk-local-unit-foundation).

Moved verbatim from WeilConjectures.AlgebraicGeometry.ConstantStalkLocalUnit, which re-exports this module, so
that the lower statements of that theorem can import them. The constructions below apply the same
canonical pullback compositors and point reparametrization to any condensed coefficient
ring, including finite extensions, directly in the ordinary module category. Localization
of a module in degree zero supplies its native derived stalk and local operator.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedModule

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing ordinary category of modules over the actual pulled-back coefficient.
Source: latest blueprint, local stalk convention
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
abbrev NativeModules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)

/-- The positive iterate of the given Weil isomorphism, using the canonical compositors.
The natural-number argument r denotes exponent r+1, as in localPositivePower.
Source: latest blueprint, theta iteration
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
@[irreducible] def nativeIterate {T : Scheme.{u}} (a : T ⟶ T) (M : NativeModules Λ T)
    (θ : (CondensedRing.upperStar Λ a).obj M ≅ M) :
    (r : ℕ) → (CondensedRing.upperStar Λ (localPositivePower a r)).obj M ≅ M :=
  isoChain (fun r ↦ (CondensedRing.upperStar Λ (localPositivePower a r)).obj M) M
    (evaluateInitial (CondensedRing.upperStar Λ (localPositivePower a 0))
      (CondensedRing.upperStar Λ a)
      (CondensedRing.upperStarCongr Λ (Eq.refl a)) M θ)
    (fun r ↦ evaluateStep
      (CondensedRing.upperStar Λ (localPositivePower a r))
      (CondensedRing.upperStar Λ a)
      (CondensedRing.upperStar Λ (localPositivePower a (r + 1)))
      (CondensedRing.upperStarComp Λ (localPositivePower a r) a) M θ)

/-- The actual return on the module stalk, including the inverse point reparametrization.
Source: latest blueprint, semilinear return, not literal fixedness
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def nativeReturn (D : FiniteFieldDatum.{u}) {T : Scheme.{u}} (a : T ⟶ T)
    (M : NativeModules Λ T) (θ : (CondensedRing.upperStar Λ a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (r : ℕ)
    (h : z ≫ localPositivePower a r =
      localPositivePower (frobeniusPointIso D).hom r ≫ z) :
    (CondensedRing.upperStar Λ z).obj M ≅ (CondensedRing.upperStar Λ z).obj M :=
  (CondensedRing.pointComparison Λ
    (CondensedRing.upperStarIsoIdOfIsSepClosed Λ
      (localPositivePower (frobeniusPointIso D).hom r))
    (localPositivePower a r) h).app M ≪≫
      (CondensedRing.upperStar Λ z).mapIso (nativeIterate Λ a M θ r)

/-- The derived stalk of a native module placed in degree zero, by exact inverse image.
Source: latest blueprint, K_xbar (blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def nativeDerivedStalk {T : Scheme.{u}} (M : NativeModules Λ T)
    {k : Type u} [Field k] (z : Spec (.of k) ⟶ T) :=
  (CondensedRing.upperStar Λ z).mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor (NativeModules Λ T) 0).obj M)

/-- Localization of the ordinary return, transported by the exact-derived single comparison.
Source: latest blueprint, local operators
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def nativeDerivedOperator (D : FiniteFieldDatum.{u}) {T : Scheme.{u}} (a : T ⟶ T)
    (M : NativeModules Λ T) (θ : (CondensedRing.upperStar Λ a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (r : ℕ)
    (h : z ≫ localPositivePower a r =
      localPositivePower (frobeniusPointIso D).hom r ≫ z) :
    End (nativeDerivedStalk Λ M z) :=
  ((CondensedRing.upperStar Λ z).mapDerivedCategorySingleFunctor 0).hom.app M ≫
    (DerivedCategory.singleFunctor _ 0).map (nativeReturn Λ D a M θ z r h).hom ≫
      ((CondensedRing.upperStar Λ z).mapDerivedCategorySingleFunctor 0).inv.app M

variable (R : Type) [CommRing R] (c : R →+* Γ Λ)

/-- Constants act on terminal sections by multiplication on the regular point module.
Source: latest blueprint, ordinary scalar stalk convention
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def nativePointScalars (k : Type u) [Field k] :
    ULift.{u + 1} R →+* (End (𝟙_ (NativeModules Λ (Spec (.of k)))))ᵐᵒᵖ :=
  (RingHom.toOpposite
    (Mod.regularEndRingHom.comp ((Γ.mapFunctor (upperStarFromPoint (Spec (.of k)))).comp c))
    (fun x y ↦ by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm])).comp
      ULift.ringEquiv.toRingHom

/-- Terminal sections, represented by Hom from the regular module, with their actual scalars.
Source: latest blueprint, Gamma(s,-) (blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def nativeSections (k : Type u) [Field k] :
    NativeModules Λ (Spec (.of k)) ⥤ ModuleCat.{u + 1} (ULift.{u + 1} R) :=
  preadditiveCoyonedaObj (𝟙_ (NativeModules Λ (Spec (.of k)))) ⋙
    ModuleCat.restrictScalars (nativePointScalars Λ R c k)

/-- Additivity of terminal sections, inherited from the representing Hom functor.
Source: latest blueprint, scalar stalk convention
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
instance nativeSections_additive (k : Type u) [Field k] :
    (nativeSections Λ R c k).Additive := inferInstanceAs
      ((preadditiveCoyonedaObj (𝟙_ (NativeModules Λ (Spec (.of k)))) ⋙
        ModuleCat.restrictScalars (nativePointScalars Λ R c k)).Additive)

/-- Terminal sections are left exact, as a represented functor followed by scalar restriction.
Source: latest blueprint, scalar stalk convention
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
instance nativeSections_limits (k : Type u) [Field k] :
    PreservesFiniteLimits (nativeSections Λ R c k) := inferInstanceAs
      (PreservesFiniteLimits (preadditiveCoyonedaObj (𝟙_ (NativeModules Λ (Spec (.of k)))) ⋙
        ModuleCat.restrictScalars (nativePointScalars Λ R c k)))

/-- At a separably closed point the regular module is projective, so sections are exact.
Source: latest blueprint, scalar stalk convention
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
instance nativeSections_colimits (k : Type u) [Field k] [IsSepClosed k] :
    PreservesFiniteColimits (nativeSections Λ R c k) := by
  let : Projective (𝟙_ (NativeModules Λ (Spec (.of k)))) :=
    ProEtale.projective_regular_of_isSepClosed (condensedRingObj Λ (Spec (.of k)))
  exact comp_preservesFiniteColimits
    (preadditiveCoyonedaObj (𝟙_ (NativeModules Λ (Spec (.of k)))))
    (ModuleCat.restrictScalars (nativePointScalars Λ R c k))

end WeilConjectures.CondensedModule


/-! # The native constant Weil stalk and its local Frobenius

Source: literature/blueprint/latest/blueprint/sec-zeta-weil/sk-thm-weil-final/
prop-every-iterate-trace.md, constant-sheaf clause
(blueprint: lem-zl-constant-stalk-local-unit-foundation).

All objects are ordinary condensed module sheaves or their ordinary derived categories.
The comparison is the coefficient-unit comparison, and scalar coordinates are normalized
by the constant section 1. Both finite-subextension and algebraic-closure coefficients
are stated together, with the actual scalar-change pullback square.
-/

@[expose] public noncomputable section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open WeilConjectures.CondensedModule
open scoped CategoryTheory.Obj

namespace WeilConjectures

namespace ConstantStalkLocalUnit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical coefficient-unit comparison in the ordinary derived category.
Source: latest blueprint, constant-sheaf clause
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def stalkIso {T : Scheme.{u}} {k : Type u} [Field k] (z : Spec (.of k) ⟶ T) :
    nativeDerivedStalk Λ (𝟙_ (NativeModules Λ T)) z ≅
      (DerivedCategory.singleFunctor (NativeModules Λ (Spec (.of k))) 0).obj (𝟙_ _) :=
  ((CondensedRing.upperStar Λ z).mapDerivedCategorySingleFunctor 0).app (𝟙_ _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ z)).symm

/-- Multiplication identifies scalar extension of the regular unit with the regular unit.
Source: latest blueprint, compatibility with E to Qbar
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def scalarUnitIso
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (Mod.extendScalars (coefficientMap a T)).obj (𝟙_ (NativeModules Λ T)) ≅
      𝟙_ (NativeModules Λ' T) :=
  letI := Mod.extendScalarsMonoidal (coefficientMap a T)
  (Functor.Monoidal.εIso (Mod.extendScalars (coefficientMap a T))).symm

/-- The canonical coefficient-unit square for scalar extension and point pullback.
Source: latest blueprint, compatibility with E to Qbar
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
@[irreducible] def ScalarCompatible
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    {T : Scheme.{u}} {k : Type u} [Field k] (z : Spec (.of k) ⟶ T) : Prop :=
  (Mod.extendScalars (coefficientMap a (Spec (.of k)))).map
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ z)).inv ≫
    (scalarUnitIso Λ a (Spec (.of k))).hom =
  (CondensedRing.pullIso a z).hom.app (𝟙_ (NativeModules Λ T)) ≫
    (CondensedRing.upperStar Λ' z).map (scalarUnitIso Λ a T).hom ≫
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ' z)).inv

variable (R : Type) [Field R] (c : R →+* Γ Λ)

/-- The scalar coordinate map, a ↦ a times the identity section of the regular module.
It fixes the canonical coordinate; the theorem asserts that this particular map is invertible.
Source: latest blueprint, terminal evaluation of the coefficient unit
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def constantSection (k : Type u) [Field k] :
    ModuleCat.of (ULift.{u + 1} R) (ULift.{u + 1} R) ⟶
      (nativeSections Λ R c k).obj (𝟙_ (NativeModules Λ (Spec (.of k)))) :=
  let N := (nativeSections Λ R c k).obj (𝟙_ (NativeModules Λ (Spec (.of k))))
  letI : AddCommGroup N := N.isAddCommGroup
  letI : Module (ULift.{u + 1} R) N := N.isModule
  ModuleCat.ofHom (Y := N) (LinearMap.toSpanSingleton (ULift.{u + 1} R) N
    ((𝟙 (𝟙_ (NativeModules Λ (Spec (.of k)))) : N)))

/-- The evaluated scalar complex, before choosing any coordinates.
Source: latest blueprint, Gamma(s,Lxbar^*Lambda_Y)
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def evaluated {T : Scheme.{u}} (D : FiniteFieldDatum.{u})
    (z : Spec (.of D.k) ⟶ T) :=
  (nativeSections Λ R c D.k).mapDerivedCategory.obj
    (nativeDerivedStalk Λ (𝟙_ (NativeModules Λ T)) z)

/-- Canonical terminal evaluation in scalar coordinates, using only the normalized unit map.
Source: latest blueprint, scalar complex Lambda[0]
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def evaluatedIso {T : Scheme.{u}} (D : FiniteFieldDatum.{u})
    (z : Spec (.of D.k) ⟶ T)
    (b : (nativeSections Λ R c D.k).obj (𝟙_ (NativeModules Λ (Spec (.of D.k)))) ≅
      ModuleCat.of (ULift.{u + 1} R) (ULift.{u + 1} R)) :
    evaluated Λ R c D z ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u + 1} (ULift.{u + 1} R)) 0).obj
        (ModuleCat.of (ULift.{u + 1} R) (ULift.{u + 1} R)) :=
  (nativeSections Λ R c D.k).mapDerivedCategory.mapIso (stalkIso Λ z) ≪≫
    ((nativeSections Λ R c D.k).mapDerivedCategorySingleFunctor 0).app (𝟙_ _) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso b

/-- Terminal evaluation of the actual returned local operator of the coefficient unit.
Source: latest blueprint, local alternating trace
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def evaluatedOperator {T : Scheme.{u}} (D : FiniteFieldDatum.{u}) (g : T ≅ T)
    (z : Spec (.of D.k) ⟶ T) (r : ℕ)
    (h : z ≫ localPositivePower g.hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ z) : End (evaluated Λ R c D z) :=
  (nativeSections Λ R c D.k).mapDerivedCategory.map
    (nativeDerivedOperator Λ D g.hom (𝟙_ (NativeModules Λ T))
      (CondensedRing.StrictWeil.unitWeilModule Λ g).str z r h)

/-- The ordinary linear trace on each scalar cohomology group of the evaluated stalk.
Source: latest blueprint, sum over j in the constant-sheaf clause
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
def cohomologyTrace {T : Scheme.{u}} (D : FiniteFieldDatum.{u}) (g : T ≅ T)
    (z : Spec (.of D.k) ⟶ T) (r : ℕ)
    (h : z ≫ localPositivePower g.hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ z) (j : ℤ) : R :=
  (LinearMap.trace (ULift.{u + 1} R)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} R)) j).obj
      (evaluated Λ R c D z))
      (((DerivedCategory.homologyFunctor _ j).map (evaluatedOperator Λ R c D g z r h)).hom)).down

/-- All clauses for one of the two coefficient fields, with canonical stalk coordinates.
Source: latest blueprint, constant Weil sheaf and each local alternating trace is 1
(blueprint: lem-zl-constant-stalk-local-unit-foundation). -/
@[irreducible] def Result {T : Scheme.{u}} (D : FiniteFieldDatum.{u}) (g : T ≅ T)
    (z : Spec (.of D.k) ⟶ T) (r : ℕ)
    (h : z ≫ localPositivePower g.hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ z) : Prop :=
  (stalkIso Λ z).inv ≫
      nativeDerivedOperator Λ D g.hom (𝟙_ (NativeModules Λ T))
        (CondensedRing.StrictWeil.unitWeilModule Λ g).str z r h ≫
      (stalkIso Λ z).hom = 𝟙 _ ∧
  ∃ b : (nativeSections Λ R c D.k).obj (𝟙_ (NativeModules Λ (Spec (.of D.k)))) ≅
      ModuleCat.of (ULift.{u + 1} R) (ULift.{u + 1} R),
    b.inv = constantSection Λ R c D.k ∧
    (evaluatedIso Λ R c D z b).inv ≫ evaluatedOperator Λ R c D g z r h ≫
      (evaluatedIso Λ R c D z b).hom = 𝟙 _ ∧
    (∀ j : ℤ, FiniteDimensional (ULift.{u + 1} R)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} R)) j).obj
        (evaluated Λ R c D z))) ∧
    (∀ j : ℤ, cohomologyTrace Λ R c D g z r h j = if j = 0 then 1 else 0) ∧
    (∑ᶠ j : ℤ, (-1 : R) ^ j * cohomologyTrace Λ R c D g z r h j) = 1

end ConstantStalkLocalUnit

end WeilConjectures
