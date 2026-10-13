/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.RingTheory.IsStrictHenselization

/-! # Strict henselization and surjective local quotients

Source: Stacks Project, Tag 05WS (strict henselization of a quotient).
(blueprint: lem-sbc-strict-henselization-surjective-quotient)
-/

@[expose] public section

universe u
namespace Algebra

/-- A surjective quotient of a local base commutes with algebraic strict henselization.
Source: Stacks Project, Tag 05WS, and the first isomorphism theorem.
(blueprint: lem-sbc-strict-henselization-surjective-quotient)

Proof: The kernel equation and surjectivity identify B with A/I. Since I is contained
in the maximal ideal of A, this quotient is local and has the same residue field as A.
Transport K through that residue-field isomorphism; its B-action factors through the
residue field, so the required scalar tower commutes. Consider the base-change functor
from etale A-algebras pointed in K to etale B-algebras pointed in K. It is final, as
follows. For a pointed etale B-algebra S, choose a standard etale principal neighbourhood
of its distinguished prime. Lift the coefficients of its standard etale presentation to
A, including the element inverted and the Jacobian determinant. The lifted presentation
is etale over A and its reduction is that neighbourhood, providing an arrow from S to
an object in the image. Given two such arrows, take the tensor product of their lifted
A-algebras, pointed by multiplying their maps to K. The two induced maps from S agree
at the distinguished point. Since S is etale over B, its diagonal is open, so these maps
agree on an open neighbourhood of that point. Choose a principal open inside this
neighbourhood and lift its denominator to the tensor product over A; it remains nonzero
in K. Inverting it gives a common refinement equalizing the two arrows. This proves
nonemptiness and connectedness of each comma category, hence finality. Extension of
scalars is left adjoint to restriction, so it preserves the universal A-algebra cocone
presenting C. Its new vertex is B tensor_A C, canonically C/IC. Finality identifies
this with the universal cocone of all pointed etale B-algebras. The vertex identification
and its structural B-map give IsStrictHenselization for the explicit quotient C/IC.
This is the pointed-algebra proof of Tag 05WS; no ring is selected from an undetermined
existence theorem. -/
theorem IsStrictHenselization.surjective_quotient
    (A K C B : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (hker : RingHom.ker π = I) :
    ∃ (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField B) L)
      (_ : IsSepClosure (IsLocalRing.ResidueField B) L)
      (_ : Algebra B L) (_ : IsScalarTower B (IsLocalRing.ResidueField B) L)
      (_ : Algebra B (C ⧸ I.map (algebraMap A C))),
      IsStrictHenselization B L (C ⧸ I.map (algebraMap A C)) := by sorry

end Algebra
