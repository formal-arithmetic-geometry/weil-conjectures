/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Supported classes using the actual condensed coefficient unit
Source: literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/sk-d-corr/
def-trf-supported-class.md (blueprint: def-trf-supported-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.TrfCondensed
/-- Discrete finite coefficients in NA's continuous-map presentation.
Source: literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/sk-d-corr/
def-trf-supported-class.md, coefficients
(blueprint: def-trf-supported-class). -/
abbrev discreteCoefficient (A : Type) [CommRing A] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  Profinite.continuousMapRingObj A

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The native unbounded derived category over the pulled-back condensed ring.
Source: literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/sk-d-corr/
def-trf-supported-class.md, D(Z,A)
(blueprint: def-trf-supported-class). -/
abbrev Ambient (T : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj Λ T))

/-- The recorded native constructible finite-Tor subcategory.
Source: literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/sk-d-corr/
lem-trf-correspondence-class.md, K and L
(blueprint: lem-trf-correspondence-class). -/
abbrev Ctf (T : Scheme.{u}) := (CondensedRing.condensedConstructibleFiniteTor Λ T).FullSubcategory

/-- The regular coefficient module, placed in degree zero.
Source: literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/sk-d-corr/
def-trf-supported-class.md, A_T[0]
(blueprint: def-trf-supported-class). -/
abbrev coefficientUnit (T : Scheme.{u}) : Ambient Λ T :=
  (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ T))

/-- The canonical derived unit comparison, induced by the regular module itself.
Source: literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/sk-d-corr/
def-trf-supported-class.md, A_T[0]
(blueprint: def-trf-supported-class). -/
def coefficientUnitIso (T : Scheme.{u}) : coefficientUnit Λ T ≅ 𝟙_ (Ambient Λ T) :=
  DerivedCategory.singleFunctorObjUnitIso _

/-- Classes supported on the specified map; no immersion or constructibility is required.
Source: literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/sk-d-corr/
def-trf-supported-class.md, displayed Hom
(blueprint: def-trf-supported-class). -/
def TraceSupportedClass {T Z : Scheme.{u}} {i : T ⟶ Z} (cs : Compactification i)
    (P : Ambient Λ Z) : Type _ :=
  (CondensedRing.rightDerivedLowerShriekOfCompactification Λ cs).obj
    (coefficientUnit Λ T) ⟶ P

/-- Change only the canonical regular-module unit presentation in the supported Hom set.
Source: literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/sk-d-corr/
def-trf-supported-class.md
(blueprint: def-trf-supported-class). -/
def supportedHomEquiv {T Z : Scheme.{u}} {i : T ⟶ Z} (cs : Compactification i)
    (P : Ambient Λ Z) : TraceSupportedClass Λ cs P ≃
      ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cs).obj (𝟙_ _) ⟶ P) :=
  Iso.homCongr ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ cs).mapIso
    (coefficientUnitIso Λ T)) (Iso.refl P)

end WeilConjectures.TrfCondensed
