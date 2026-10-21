/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.Paper.SfClopenRestrictionData
import Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus

/-! # Normalized derived reduction and completeness on a clopen component

Source: Stacks Project, Tags 06YY, 08TC and 08FZ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Exact ordinary restriction to a clopen preserves the actual normalized quotient
complexes, their augmented towers, derived completeness and objectwise residue Tor bounds.

Source: Stacks Project, Tags 06YY, 08TC and 08FZ
(blueprint: lem-sf-clopen-derived-compatibility).
Proof: use the two-component partition into U and its open complement. The finite-clopen
module equivalence and derived tensor calculus make ordinary restriction exact and
identify its unbounded derived functor with the corresponding coordinate projection.
The finite and completed coefficient identifications in d commute with the quotient
projections; on each test object this identifies the scalar-extension tensors by
s tensor x mapped to the local s tensor x. Sheafification gives the ordinary natural
isomorphism; degreewise application gives finite_quotient and quotient with the recorded
pure-tensor normalizations. Descend the ordinary comparison through K-flat localization
to obtain reduction. Uniqueness of left derived functors with their universal comparison
makes its counit square commute on every complex; this is a square of derived-functor
comparison transformations, so the assertion is not limited to K-flat inputs.
The tensor formula commutes with the coefficient quotient transitions and with the unit
x mapped to 1 tensor x. Localizing therefore gives the tower natural isomorphism with
its prescribed components and the augmented unit square. Restriction preserves K-flat
complexes and flat terms by the tensor calculus. Under the finite-product derived
equivalence, insertion in the U coordinate is left adjoint to restriction, so restriction
preserves all existing products, in particular the product used in the Roos triangle.
Its exact derived functor preserves that triangle, the map 1 minus the transition shift,
and the augmentation. A global K-flat completeness witness thus restricts to a local
one with the same Roos limit condition. Finally a local site object V has the same
underlying object over T; relocalization identifies their slice categories and restricted
coefficient rings. The residue reduction comparison identifies tensoring with every
local degree-zero module. Transport the assumed vanishings through these exact slice
and tensor identifications; the integers a and b do not change. Empty components give
zero categories and satisfy the same argument. -/
theorem sf_clopen_derived_compatibility
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{t}) (U : T.Opens)
    (hU : IsClosed (U : Set T)) (d : SfClopenCoefficientRestriction l E T U) :
    Nonempty (SfClopenCompleteRestriction d) := by
  sorry

end WeilConjectures
