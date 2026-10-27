/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.LisseLatticeHeartLiftData

/-! # Every normalized raw realization is full and faithful on finite-type geometric bases. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.LisseLattice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Every normalized raw realization is full and faithful on finite-type geometric bases.
Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2).

Proof: finite type over the field supplies noetherianity, finite dimension, and l a unit.
Normalized coefficient transport and the integral characterization identify the intrinsic
integral constructible category with the completed integral category used in the rational
Hom comparison. That comparison at shift zero identifies the localized integral Hom
module with the ambient derived Hom. Its fraction map is a tensor f sent to a times
F(f). The residues fix completion uniquely, and the localization unit fixes the rational
coefficient identification uniquely, so these are precisely the scalar maps of a.
Naturality of a.integral identifies J on integral maps with F, and a.fractions identifies
it on every pure tensor. Every localized Hom is generated additively by pure tensors;
J is additive, so its Hom maps agree with the comparison on all morphisms. The Hom
bijection supplies fullness and faithfulness. This applies to every normalized a and
does not assume a is a preselected realization or that an integral lattice is free.
(blueprint: lem-tw-lisse-lattice-realization-faithful). -/
theorem normalized_realization_fully_faithful (D : FiniteFieldDatum.{u})
    (hl : l ≠ D.p) (X : LisseRealization.Base D l hl) (a : RealizationAt l E X.scheme) :
    a.J.Full ∧ a.J.Faithful := by sorry

end WeilConjectures.LisseLattice
