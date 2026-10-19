/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.IntegralModelsDefinitions
public import Sheaf.Paper.IntegralModelsResidueRealization

/-! # Cohomological comparison for the first embedded residue

Source: blueprint main-20261015, sk-lem-integral-models, proof steps 4--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The constant first reduction and the specified continuous first reduction have the
same constructible cohomology condition. Over the residue field finite Tor amplitude
corresponds exactly to bounded cohomology. No completeness or etale-origin predicate
occurs in this coefficient comparison.

Source: blueprint main-20261015, sk-lem-integral-models, proof steps 4--5;
Stacks Tags 03ET, 06YQ, 099I and 099L.
(blueprint: lem-sfb-embedded-integral-residue-comparison).

Proof: the first quotient is the finite residue field, since pi generates the maximal
ideal. Its quotient topology is discrete. The constant-to-continuous map on this
finite ring is an isomorphism: a continuous function is constant on its clopen fibres,
and those fibres form a finite cover. The integral scalar map is flat and induces the
identity on the first quotient, so its finite derived-reduction comparison identifies
reduction after restriction with direct continuous reduction. On pure tensors this
comparison keeps the residue scalar and underlying module section unchanged. Apply the
section-action equivalence and restrict to constant functions. This gives precisely the
specified intrinsic realization, since the continuous chart is normalized on constant
functions. The realization is exact, as its composite with the faithful exact additive
forgetful functor is the additive forgetful functor before restriction. Thus it preserves
cohomology and reflects its vanishing. The constant finite local models on every stratum
correspond to the intrinsic finite local models, with their original finite partition.
Finally all module sheaves over a constant field are flat: their presheaf sections are
vector spaces and flat sheafification preserves flatness. Good truncations represent a
bounded complex by a bounded complex of flat objects, whose tensor computes its derived
tensor. This proves finite Tor amplitude in the same interval. Tensor with the unit
proves the converse. Enlarge the interval to an ordered interval when necessary,
including for zero objects. Empty schemes are included throughout. -/
theorem embeddedIntegral_residue_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    [Finite (completedResidue ℓ E π 0)] [DiscreteTopology (completedResidue ℓ E π 0)]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (integralCoefficientObject X ℓ E))) :
    integralModelConstantResidueCondition X ℓ E π
      ((IntegralModelsEmbedded.restriction.{u} ℓ E X).obj K) ↔
    integralModelIntrinsicBoundedConstructible X (completedResidue ℓ E π 0)
      ((integralModelIntrinsicDerivedRealization.{u} X (completedResidue ℓ E π 0)).obj
        ((integralModelFirstDerivedReduction X ℓ E π).obj K)) := by sorry

end AlgebraicGeometry.ProEtale
