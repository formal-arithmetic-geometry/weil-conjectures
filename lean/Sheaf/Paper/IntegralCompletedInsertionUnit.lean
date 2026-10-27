/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T8
-/
module

public import Sheaf.Paper.PulledReductionComparisonData

/-! # Transport of the completed scalar insertion

Source: current blueprint, det-lem-int-tensor-pullback, first paragraph and comparison
paragraph; Stacks sites-modules.tex, lemma-adjoint-push-pull-modules.
(blueprint: lem-sfb-integral-completed-insertion-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralAugmentedQuotient

/-- The completed scalar-insertion section becomes the canonical module pullback unit
under the equality of the two published pullback functors. The equality proof is an
explicit argument, so the statement uses no private comparison definition.
Source: det-lem-int-tensor-pullback.proof.md, first paragraph and Comparison with the
Stacks Project; step 1 of lem-sfb-integral-augmented-quotient-towers;
Stacks sites-modules.tex, lemma-adjoint-push-pull-modules
(blueprint: lem-sfb-integral-completed-insertion-unit).

Proof: the projection-defined coefficient map equals the prescribed integralRingIso
map, since both composites with every finite quotient projection agree. The completed
pullback is inverse image followed by its published scalar-extension functor. Its
ordinary object equality with the sheafified tensor construction is reductionChange_obj_eq;
the map equality is reductionChange_map_eq. These equations identify the functor equality
in the statement with the natural isomorphism whose components are those object equalities:
functor equalities and object equalities are propositions, so their proofs are irrelevant.
By the sheafified tensor-unit formula, that natural isomorphism carries the scalar insertion
to the image of 1 tensor the model-site inverse-image adjunction unit. The canonical
identified-coefficient module adjunction is the composite of inverse-image adjunction and
scalar-extension adjunction. Its unit on the section x is the same tensor 1 tensor x.
The restriction at the identity map of the base-changed object is the identity, by the
module presheaf identity axiom. Thus both sections agree. This applies to every module
and every site object, including the empty object and the zero module, and is independent
of the chosen equality proof by proof irrelevance. No finite quotient or complex is used.
-/
theorem completedInsertionUnit
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (h : completedModulePullback g d =
      proEtaleRingModulePullback g (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso g))
    (M : reductionModules Y (d.completedRing Y)) (Z : Y.ProEtᵒᵖ)
    (x : M.val.obj Z) :
    ((eqToIso h).hom.app M).val.app ((proEtaleBaseChange g).op.obj Z)
        (PulledReduction.insertion d g M Z x) =
      ((proEtaleRingModuleAdjunction g (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso g)).unit.app M).val.app Z x := by sorry

end WeilConjectures.IntegralAugmentedQuotient
