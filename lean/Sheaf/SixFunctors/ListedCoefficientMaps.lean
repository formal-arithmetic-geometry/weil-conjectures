/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.CartesianCoefficients
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-! # The listed coefficient maps

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/_section.md,
coefficient list (1)--(4) (blueprint: def-sfb-listed-coefficient-maps).

The generators retain their actual ring-object maps. Finite maps are characterized
by postcomposition on sections, so no flatness or surjectivity is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The specified continuous map O_E to a finite discrete ring, as postcomposition
on all profinite sections. The valuation topology is the existing restricted topology.
Source: blueprint coefficient list (3)
(blueprint: def-sfb-listed-coefficient-maps). -/
def IsIntegralFiniteScalarMap (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (A : Type u) [CommRing A]
    (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
      ⟨cartesianFinitePointRing A⟩) : Prop :=
  letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
  ∃ φ : PadicAlgCl.integers ell E.1 →+* A,
    @Continuous _ _ inferInstance ⊥ φ ∧
    ∀ (P : Profinite.{u}) (s : ULift.{u + 1} C(P, PadicAlgCl.integers ell E.1))
      (x : P), ((a.hom.hom.hom.app (op P)) s).down x = φ (s.down x)

/-- Exactly the six elementary kinds of listed coefficient map and their finite
composites. Finite rings are killed by an ell-power; the zero ring is allowed.
The algebraic closure has the finite-subextension-valued condensed convention.
The identity of that endpoint is included as the empty composite; identities of
finite, integral and field endpoints already occur among the corresponding generators.
Source: blueprint coefficient list (1)--(4)
(blueprint: def-sfb-listed-coefficient-maps). -/
inductive ListedCoefficientMap (ell : ℕ) [Fact ell.Prime] :
    {Λ Λ' : ScalarSixRing.{u}} → (Λ ⟶ Λ') → Prop
  | finite (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
      (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
      (hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0)
      (φ : A →+* B)
      (a : (⟨cartesianFinitePointRing A⟩ : ScalarSixRing.{u}) ⟶
        ⟨cartesianFinitePointRing B⟩)
      (ha : ∀ (P : Profinite.{u}) (s : (cartesianFinitePointRing A).obj.obj (op P)) (x : P),
        ((a.hom.hom.hom.app (op P)) s).down x = φ (s.down x)) :
      ListedCoefficientMap ell a
  | integers (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicIntegersRingObj ell F.1⟩)
      (ha : a.hom.hom = finiteCoefficientIntegersPointMap ell h) :
      ListedCoefficientMap ell a
  | fields (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (a : (⟨Profinite.continuousMapRingObj E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.continuousMapRingObj F.1⟩)
      (ha : a.hom.hom = Profinite.padicSubfieldRingObjMap ell h) :
      ListedCoefficientMap ell a
  | localization (E : PadicAlgCl.FiniteIntermediateField ell)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.continuousMapRingObj E.1⟩)
      (ha : a.hom.hom = (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ell E.1)) :
      ListedCoefficientMap ell a
  | algebraicClosure (E : PadicAlgCl.FiniteIntermediateField ell)
      (a : (⟨Profinite.continuousMapRingObj E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicAlgClRingObj ell⟩)
      (ha : a.hom.hom = Profinite.padicSubfieldRingObjToPadicAlgCl ell E) :
      ListedCoefficientMap ell a
  | integralFinite (E : PadicAlgCl.FiniteIntermediateField ell)
      (A : Type u) [CommRing A] [Finite A]
      (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨cartesianFinitePointRing A⟩)
      (ha : IsIntegralFiniteScalarMap ell E A a) : ListedCoefficientMap ell a
  | algebraicClosureIdentity :
      ListedCoefficientMap ell (𝟙 (⟨Profinite.padicAlgClRingObj ell⟩ : ScalarSixRing.{u}))
  | comp {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
      (ha : ListedCoefficientMap ell a) (hb : ListedCoefficientMap ell b) :
      ListedCoefficientMap ell (a ≫ b)

end AlgebraicGeometry.ProEtale.CondensedRing
