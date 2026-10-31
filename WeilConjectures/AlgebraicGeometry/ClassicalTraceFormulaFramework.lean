/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFormulaCoefficientSetup
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import WeilConjectures.AlgebraicGeometry.GeometricOperations
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.ModuleHomComplex

/-! # Classical framework conventions for the trace formula

Source: `literature/blueprint/latest/blueprint/sec-trace-formula/sk-d-six/
rem-trf-classical-framework.md`, node rem-trf-classical-framework, order 3701
(blueprint: rem-trf-classical-framework).

The structure records the ordinary finite-coefficient operation package and the
perfect-complex trace data used by the classical framework.  The coefficient
rings, pulled-back condensed coefficients, constructible predicates, ordinary
derived categories, total tensor, total Hom, and mates are the recorded
constructions imported above; this declaration does not introduce alternative
versions of any of them.  In particular, the operation package is restricted
to its supplied bounded constructible finite-Tor domains, and the trace domain
is the recorded perfect-complex predicate.

## Main definitions

* `ClassicalTraceFormulaFramework`: the fixed datum and supplied ordinary operation package.
* Its namespace provides transparent chapter notation for the existing condensed categories,
  scalar extension, signed tensor and total Hom, together with the specified point trace.
  These abbreviations reuse the dependency constructions, rather than constructing new categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Fixed geometric, coefficient and ordinary operation data for the chapter.
The positive level is `n + 1`; the field is a finite subextension of the fixed
algebraic closure. All operation domains and component coherence laws are those
of the recorded `GeometricOperations` package. There is no functorial cone,
additional exceptional domain, or implicit coherence field.
Source: latest blueprint, rem-trf-classical-framework, clauses 1--2
(blueprint: rem-trf-classical-framework). -/
structure ClassicalTraceFormulaFramework where
  datum : FiniteFieldDatum.{u}
  coefficients : datum.CoefficientDatum
  field : IntermediateField (Padic coefficients.l) coefficients.Qbar
  [finite : FiniteDimensional (Padic coefficients.l) field]
  n : ℕ
  setup : TraceFormulaCoefficientSetup datum coefficients.l coefficients.different field
    (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  exceptional : GeometricOperationPackage.ExceptionalAdjunctions datum coefficients.l
    coefficients.different field n setup
  operations : GeometricOperations datum coefficients.l coefficients.different field n
    setup exceptional

attribute [instance] ClassicalTraceFormulaFramework.finite

namespace ClassicalTraceFormulaFramework

/-- The point trace is the recorded trace `finiteCoefficientCategoricalTrace` of
`def-trf-categorical-trace` on perfect complexes at the positive finite coefficient
level fixed by `T`.  Its dual, evaluation, coevaluation, scalar identification and
Koszul symmetry are the recorded constructions; chain identities and representative
independence are separate results.
Source: latest blueprint, rem-trf-classical-framework, clause 3
(blueprint: rem-trf-classical-framework). -/
noncomputable def pointTrace (T : ClassicalTraceFormulaFramework.{u})
    (P : DerivedCategory
      (ModuleCat.{u} (Padic.coefficientExtensionRing T.coefficients.l T.field (T.n + 1))))
    (hP : DerivedCategory.IsPerfectRingComplex P) (v : P ⟶ P) :
    Padic.coefficientExtensionRing T.coefficients.l T.field (T.n + 1) :=
  finiteCoefficientCategoricalTrace T.datum T.coefficients T.field (T.n + 1)
    (Nat.succ_le_succ (Nat.zero_le T.n)) P hP v

/-- Chapter notation for the pulled-back condensed coefficient ring.
Source: latest blueprint, rem-trf-classical-framework, clauses 1 and 4
(blueprint: rem-trf-classical-framework). -/
abbrev coefficient (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) :=
  AlgebraicGeometry.ProEtale.coefficientRing X Λ

/-- Chapter notation for the ordinary localization at quasi-isomorphisms on the
small pro-etale site. Its shift and distinguished triangles are the existing
`DerivedCategory` structures; this notation supplies no cone functor.
Source: latest blueprint, rem-trf-classical-framework, clause 1
(blueprint: rem-trf-classical-framework). -/
abbrev derived (Λ : Profinite.CondensedRing.{u}) (X : Scheme.{u}) :=
  DerivedCategory (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (coefficient Λ X).X)

/-- Chapter notation for the full bounded constructible category, with morphisms
in the ordinary ambient derived category, for every admissible coefficient stage.
Source: latest blueprint, rem-trf-classical-framework, clauses 1 and 4
(blueprint: rem-trf-classical-framework). -/
abbrev boundedConstructible (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) :=
  AlgebraicGeometry.ProEtale.ConstantModelBoundedConstructible Λ.X X

/-- Chapter notation for the full finite-Tor subcategory of bounded constructible
objects. Its predicate is the recorded finite-Tor predicate, not finite cohomology.
Source: latest blueprint, rem-trf-classical-framework, clauses 1 and 4
(blueprint: rem-trf-classical-framework). -/
abbrev boundedConstructibleFiniteTor (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) :=
  AlgebraicGeometry.ProEtale.ConstantModelConstructibleFiniteTor Λ.X X

/-- The algebraically closed coefficient is the existing finite-subextension-valued
continuous-function sheaf, pulled back from the point, without an inverse-system model.
Source: latest blueprint, rem-trf-classical-framework, clauses 1 and 4
(blueprint: rem-trf-classical-framework). -/
abbrev algebraicallyClosedCoefficient (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) X

/-- A reduction, localization or field-extension passage denotes derived scalar
extension along the pulled-back coefficient morphism. Existence of lattices and
finite-field descent are separate theorems, not fields of this convention.
Source: latest blueprint, rem-trf-classical-framework, clause 4
(blueprint: rem-trf-classical-framework). -/
abbrev coefficientPassage
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u}) :=
  (CategoryTheory.Mod.extendScalars
    (AlgebraicGeometry.ProEtale.coefficientMap a X)).leftDerivedFunctor

/-- Explicit tensor representatives use the recorded signed totalization, with
second differential `(-1)^p (1 ⊗ d)` and the Koszul braiding. Associators and
unitors retain their ordinary types; no strict associativity is imposed.
Source: latest blueprint, rem-trf-classical-framework, clause 5
(blueprint: rem-trf-classical-framework). -/
abbrev cochainTensor (R : Type u) [CommRing R]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :=
  CochainComplex.mapBifunctor P Q (curriedTensor (ModuleCat.{u} R))

/-- Explicit Hom representatives use the existing differential
`d_M z - (-1)^j z d_L`. Into the degree-zero unit this gives the dual differential
`(-1)^(j+1)`, with the evaluation and coevaluation used by `pointTrace`.
Source: latest blueprint, rem-trf-classical-framework, clause 5
(blueprint: rem-trf-classical-framework). -/
abbrev cochainHom (R : Type u) [CommRing R]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :=
  CochainComplex.moduleHomComplex P Q

/-- The ordinary exceptional unit, on precisely the supplied adjunction domain.
Source: latest blueprint, rem-trf-classical-framework, clause 2
(blueprint: rem-trf-classical-framework). -/
abbrev exceptionalUnit (T : ClassicalTraceFormulaFramework.{u})
    {X Y : TraceFormulaGeometricSpace T.datum} (f : X ⟶ Y) :=
  (T.exceptional f).unit

/-- The ordinary exceptional counit, on precisely the supplied adjunction domain.
Source: latest blueprint, rem-trf-classical-framework, clause 2
(blueprint: rem-trf-classical-framework). -/
abbrev exceptionalCounit (T : ClassicalTraceFormulaFramework.{u})
    {X Y : TraceFormulaGeometricSpace T.datum} (f : X ⟶ Y) :=
  (T.exceptional f).counit

end ClassicalTraceFormulaFramework
end WeilConjectures
