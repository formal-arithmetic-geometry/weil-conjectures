/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.CommonFieldLatticeGenerators

/-! # The listed scalar coefficient maps

Source: blueprint sec-six-functors-basics/sk-prop-scalar-six, coefficient list (1)--(4).
(blueprint: def-sfb-listed-scalar-coefficient-maps).

The inductive predicate includes only the displayed primitive maps, their finite
composites, and changes of ring presentation by isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Bundle the existing continuous-function condensed ring, without changing its data.
Source: blueprint scalar-six, topological coefficients
(blueprint: def-sfb-listed-scalar-coefficient-maps). -/
abbrev scalarSixTopologicalRing (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : ScalarSixRing.{u} :=
  ⟨Profinite.continuousMapRingObj A⟩

/-- Postcomposition with the specified continuous ring map, as a bundled ring-object map.
Source: blueprint scalar-six, coefficient maps (1)--(3)
(blueprint: def-sfb-listed-scalar-coefficient-maps). -/
def scalarSixContinuousMap {A B : Type} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    scalarSixTopologicalRing.{u} A ⟶ scalarSixTopologicalRing B :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap f hf)⟩⟩

/-- The finite subfield coefficient ring with its inherited norm topology.
Source: blueprint scalar-six, coefficient list (2)
(blueprint: def-sfb-listed-scalar-coefficient-maps). -/
abbrev scalarSixFieldRing (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) : ScalarSixRing.{u} :=
  ⟨Profinite.continuousMapRingObj E⟩

/-- The integral-to-field localization, using the published continuous inclusion.
Source: blueprint scalar-six, coefficient list (3)
(blueprint: def-sfb-listed-scalar-coefficient-maps). -/
def scalarSixIntegralToField (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    latticeIntegralRing.{u} ell E ⟶ scalarSixFieldRing ell E :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ell E.1)⟩⟩

/-- The coefficient maps listed in scalar-six, with finite composition. Finite
admissible rings are discrete finite commutative rings killed by a power of ell.
The isomorphism rule changes presentations, not the underlying coefficient map.
Source: blueprint scalar-six, coefficient list (1)--(4)
(blueprint: def-sfb-listed-scalar-coefficient-maps). -/
inductive IsListedScalarCoefficientMap (ell : ℕ) [Fact ell.Prime] :
    {Λ Λ' : ScalarSixRing.{u}} → (Λ ⟶ Λ') → Prop
  | finite {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [DiscreteTopology A] [Finite A] [CommRing B] [TopologicalSpace B]
      [IsTopologicalRing B] [DiscreteTopology B] [Finite B]
      (n m : ℕ) (hA : (ell : A) ^ n = 0) (hB : (ell : B) ^ m = 0)
      (f : A →+* B) (hf : Continuous f) :
      IsListedScalarCoefficientMap ell (scalarSixContinuousMap f hf)
  | integral {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
      IsListedScalarCoefficientMap ell (latticeIntegralMap ell h)
  | field {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
      IsListedScalarCoefficientMap ell
        (⟨⟨Profinite.padicSubfieldRingObjMap ell h⟩⟩ :
          scalarSixFieldRing ell E ⟶ scalarSixFieldRing ell F)
  | localization (E : PadicAlgCl.FiniteIntermediateField ell) :
      IsListedScalarCoefficientMap ell (scalarSixIntegralToField ell E)
  | algebraicClosure (E : PadicAlgCl.FiniteIntermediateField ell) :
      IsListedScalarCoefficientMap ell
        (⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩⟩ :
          scalarSixFieldRing ell E ⟶ latticeClosureRing ell)
  | integralFinite (E : PadicAlgCl.FiniteIntermediateField ell)
      {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [DiscreteTopology A] [Finite A] (n : ℕ) (hA : (ell : A) ^ n = 0)
      (f : PadicAlgCl.integers ell E.1 →+* A) (hf : Continuous f) :
      IsListedScalarCoefficientMap ell (scalarSixContinuousMap f hf)
  | comp {Λ Λ' Λ'' : ScalarSixRing.{u}} {a : Λ ⟶ Λ'} {b : Λ' ⟶ Λ''}
      (ha : IsListedScalarCoefficientMap ell a) (hb : IsListedScalarCoefficientMap ell b) :
      IsListedScalarCoefficientMap ell (a ≫ b)
  | iso {Λ Λ' Γ Γ' : ScalarSixRing.{u}} (e : Γ ≅ Λ) (e' : Λ' ≅ Γ')
      {a : Λ ⟶ Λ'} (ha : IsListedScalarCoefficientMap ell a) :
      IsListedScalarCoefficientMap ell (e.hom ≫ a ≫ e'.hom)

end AlgebraicGeometry.ProEtale.CondensedRing
