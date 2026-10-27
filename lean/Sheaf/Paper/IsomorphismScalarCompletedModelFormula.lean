/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.IsomorphismScalarCompletedModelBase

/-! # Completed pure-tensor comparison

Source: Stacks Project, sites-modules.tex, Tag 03EL; sites-cohomology.tex, Tag 0G7E;
Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4).
(blueprint: lem-weil-isomorphism-scalar-completed-formula).

The proof composes the coefficient square at every finite projection, applies the
inverse-limit scalar-chain comparison, transports its normalized pure-tensor rule
through the specified completed presentations, and restricts to the good-complex
subcategory. The resulting local section equation is precisely CompletedFormula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings
namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- Existence of the completed chain isomorphism with its normalized pure-tensor
formula. This is the comparison component of the completed model statement.

Source: Stacks Project, sites-modules.tex, Tag 03EL; sites-cohomology.tex, Tag 0G7E;
Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4).
(blueprint: lem-weil-isomorphism-scalar-completed-formula).

Proof: Compose the two maps from inverse image of the completed E coefficient ring
into the completed L coefficient ring with every finite projection. The projection
formula for inverseImageCompletedCoefficientMap, naturality of the finite constant
coefficient comparisons, and the residue formula for completedCoefficientMap make
these composites equal. Joint monicity of the limit projections gives the coefficient
square. Apply limitScalarChainComparison to the finite E and L coefficient towers.
Identify its scalar-extension functors with completedOrdinaryScalarExtension using
their specified object equalities to sheafified changeOfRings and their conjugated
map equalities. These object equalities give natural isomorphisms, and their inverses
transport the sheafification-unit pure tensors to completedScalarTensorSection.
Transport the comparison through these isomorphisms and restrict to good complexes.
Its forward pure-tensor rule is exactly CompletedFormula. The argument applies to
unbounded complexes, including the zero complex and an empty site.
-/
theorem scalar_completed_formula
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g,
      CompletedFormula l E L ι g b := by sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
