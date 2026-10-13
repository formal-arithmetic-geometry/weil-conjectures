/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.RingTheory.IsStrictHenselization
import Sheaf.RingTheory.StrictHenselizationTriples

/-!
# Local structure of a ring strict henselization

Source: Stacks Project, Tags 04GP(2),(4) and 04GW
(blueprint: lem-sc-ring-strict-henselization-local-maximal-ideal).
-/

@[expose] public section

universe u

namespace Algebra

/-- A strict henselization is local, with maximal ideal extended from the base.
Source: Stacks Project, Tags 04GP(2),(4) and 04GW
(blueprint: lem-sc-ring-strict-henselization-local-maximal-ideal).

Proof: Set p to the closed point of Spec A. Identify its scheme residue field with
A's residue field and transport the given separable closure structure to it.
A pointed etale A-algebra S with map f : S → K determines the triple whose prime
is ker f and whose residue embedding sends s/t to f(s)/f(t). The denominator is
nonzero since t is outside ker f. Its prime lies over p because f restricts to
the canonical map A → K. Conversely a triple gives its structural map to K by
composition through its residue field. The two constructions are inverse up to
canonical isomorphism: a field homomorphism is injective, and fraction-field
extension uniquely determines the residue embedding. Morphisms on both sides
are exactly A-algebra maps commuting with these maps to K. This gives an
equivalence of index categories intertwining the underlying ring diagrams.
The forgetful functor from A-algebras to rings preserves the colimit (the
structural map from A is induced by the compatible stage maps). Apply
Scheme.strictHenselization_triples to obtain a local ring T and a structural
map rho : A → T with maximalIdeal T = (maximalIdeal A).map rho. Transport its
colimit along the equivalence just described. Uniqueness of colimits gives an
A-algebra isomorphism T ≃ₐ[A] C. Transport locality along this ring isomorphism.
An isomorphism preserves units, hence carries the maximal ideal to the maximal
ideal; its A-linearity identifies the image of rho with algebraMap A C.
Consequently maximalIdeal C = (maximalIdeal A).map (algebraMap A C).
No Noetherian assumption or completion theorem is used. -/
theorem strictHenselization_local_maximalIdeal
    (A K C : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    ∃ (_ : IsLocalRing C),
      IsLocalRing.maximalIdeal C = (IsLocalRing.maximalIdeal A).map (algebraMap A C) := by
  sorry

end Algebra
