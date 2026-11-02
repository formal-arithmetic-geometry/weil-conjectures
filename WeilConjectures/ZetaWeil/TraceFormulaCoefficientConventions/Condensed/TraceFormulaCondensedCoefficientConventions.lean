/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.TraceFormulaCoefficientConventions.TraceFormulaCoefficientData
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Condensed trace-formula coefficient conventions

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-coefficients-constructible/sec-n-brown/sk-thm-existence/
def-trf-coefficient-conventions.md (blueprint: def-trf-coefficient-conventions).

All operations below specialize the recorded condensed constructions to the discrete
finite quotient A. The shared data is defined once in TraceFormulaCoefficientData.
The namespace distinguishes this current interface from published finite-model users.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.TraceFormulaCoefficientConventions
namespace Condensed

/-- The actual condensed coefficient ring of continuous functions into discrete A.
The topology is fixed in the construction, with no hidden topological hypothesis.
Source: blueprint def-trf-coefficient-conventions, A on the small pro-etale site.
(blueprint: def-trf-coefficient-conventions). -/
abbrev coefficient (T : TraceFormulaCoefficientConventions.{u}) :=
  letI : TopologicalSpace T.coefficientRing := ⊥
  letI : DiscreteTopology T.coefficientRing := ⟨rfl⟩
  Profinite.continuousCoefficientRingObj T.coefficientRing

/-- The ordinary unbounded category of modules over the pulled-back condensed ring.
Source: blueprint def-trf-coefficient-conventions, ambient category.
(blueprint: def-trf-coefficient-conventions). -/
abbrev ambient (T : TraceFormulaCoefficientConventions.{u}) (Y : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (coefficient T) Y))

/-- Bounded constructibility on the actual condensed module category.
Source: blueprint def-trf-coefficient-conventions, D^b_c(X,A).
(blueprint: def-trf-coefficient-conventions). -/
abbrev boundedConstructible (T : TraceFormulaCoefficientConventions.{u}) :=
  AlgebraicGeometry.ProEtale.boundedConstructible
    (condensedRingObj (coefficient T) T.geometricBaseChange)

/-- The recorded finite-Tor subcategory, specialized to discrete A.
Source: blueprint def-trf-coefficient-conventions, D^b_ctf(X,A).
(blueprint: def-trf-coefficient-conventions). -/
abbrev boundedConstructibleFiniteTor (T : TraceFormulaCoefficientConventions.{u}) :=
  CondensedRing.condensedConstructibleFiniteTor (coefficient T) T.geometricBaseChange

/-- Total derived pullback of modules over the pulled-back condensed coefficient ring.
Source: blueprint def-trf-coefficient-conventions, derived pullback.
(blueprint: def-trf-coefficient-conventions). -/
def derivedPullback (T : TraceFormulaCoefficientConventions.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) : ambient T Z ⥤ ambient T Y :=
  (CondensedRing.upperStar (coefficient T) f).leftDerivedFunctor

/-- The recorded condensed relative derived tensor, with both variables retained.
Source: blueprint def-trf-coefficient-conventions, derived tensor.
(blueprint: def-trf-coefficient-conventions). -/
abbrev derivedTensor (T : TraceFormulaCoefficientConventions.{u}) :=
  CondensedRing.derivedTensor (coefficient T) T.geometricBaseChange

/-- The recorded condensed relative derived internal Hom, contravariant in its first input.
Source: blueprint def-trf-coefficient-conventions, derived internal Hom.
(blueprint: def-trf-coefficient-conventions). -/
abbrev derivedInternalHom (T : TraceFormulaCoefficientConventions.{u}) :=
  CondensedRing.derivedHom (coefficient T) T.geometricBaseChange

/-- Cohomology module sheaves in every integer degree of the condensed derived category.
Source: blueprint def-trf-coefficient-conventions, cohomology sheaves.
(blueprint: def-trf-coefficient-conventions). -/
abbrev cohomologySheaf (T : TraceFormulaCoefficientConventions.{u}) (i : ℤ) :=
  DerivedCategory.homologyFunctor
    (Mod (Sheaf (Scheme.ProEt.topology T.geometricBaseChange) Ab.{u + 1})
      (condensedRingObj (coefficient T) T.geometricBaseChange)) i

/-- Constant sections give the canonical A-action on the global-section presentation.
Source: blueprint def-trf-coefficient-conventions, finite coefficients A.
(blueprint: def-trf-coefficient-conventions). -/
def scalarAction (T : TraceFormulaCoefficientConventions.{u}) :
    ULift.{u + 1, u} T.coefficientRing →+* MonObj.Γ (coefficient T) := by
  letI : TopologicalSpace T.coefficientRing := ⊥
  letI : DiscreteTopology T.coefficientRing := ⟨rfl⟩
  exact (Sheaf.ringHomΓSheafCompose (coherentTopology Profinite.{u})
    (Profinite.continuousCoefficientRingSheaf T.coefficientRing)
    (fun S ↦ ULift.ringEquiv.symm.toRingHom.comp
      (ContinuousMap.C (α := S.unop) (R := T.coefficientRing)
        (A := T.coefficientRing))) (fun _ _ ↦ rfl)).comp ULift.ringEquiv.toRingHom

/-- RΓ_c(X,K) is the recorded condensed compact coefficient complex Fib_s(Ra_X!K),
with its canonical A-action given by constant sections.
Source: blueprint def-trf-coefficient-conventions, first displayed formula.
(blueprint: def-trf-coefficient-conventions). -/
def compactSupportComplex (T : TraceFormulaCoefficientConventions.{u})
    (c : Compactification T.structureMap)
    (K : (boundedConstructible T).FullSubcategory) :
    DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing)) :=
  (ModuleCat.restrictScalars (scalarAction T)).mapDerivedCategory.obj
    ((CondensedRing.condensedRingCompactCoefficientComplex (coefficient T) c).obj K.obj)

/-- H_c^i(X,K) is the recorded compact cohomology with its canonical A-action.
Restriction of scalars is exact, so it commutes with the cohomology of RΓ_c.
Source: blueprint def-trf-coefficient-conventions, second displayed formula.
(blueprint: def-trf-coefficient-conventions). -/
def compactSupportCohomology (T : TraceFormulaCoefficientConventions.{u})
    (c : Compactification T.structureMap)
    (K : (boundedConstructible T).FullSubcategory) (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1, u} T.coefficientRing) :=
  (ModuleCat.restrictScalars (scalarAction T)).obj
    ((CondensedRing.condensedRingCompactCohomology (coefficient T) c i).obj K.obj)

end Condensed
end WeilConjectures.TraceFormulaCoefficientConventions
