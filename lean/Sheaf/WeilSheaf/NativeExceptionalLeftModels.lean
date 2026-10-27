/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalForgetfulData

/-! # NativeExceptionalLeftModels

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.AdicQbarRealization
namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

/-- The ordinary derived forgetful functors factor through the common-stage
constructible categories. The normalized left comparison admits representing counit lifts.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, exceptional
adjunction sentence; native comparison proof Steps 1--2.
(blueprint: lem-sf-native-exceptional-left-models).

Proof: use the exact native forgetting comparison to test bounded constructibility
on the underlying complex. Transport along closureMap, an isomorphism over the model,
preserves this predicate. The essential-image assertion and full faithfulness of
Family.data lift each U to the common-stage category, on all derived morphisms.
For the chosen native compactification, compose the open/proper forgetful comparison
with the inverse of the scalar-normalized compact-support realization. The latter is
normalized by the integral proper mate and open unit. Closure transport and
compactification refinement identify this with the operation of any specified
coefficient system and compactification. Lift the resulting natural isomorphism
through the fully faithful realization on the target. Retain this normalized left
comparison a. Native open/proper forgetting identifies the Grothendieck fixed-pair
hearts and the exact Frobenius action. The scalar counit lemma gives an invertible
Frobenius mate and its invariant counit. The normalized cyclic derived Hom sequence
is compatible with exact open and right-derived proper images by its finite
composite functoriality theorem. Apply cyclicDerived_liftedCounit_represents on the
bounded constructible full subcategories. Its degree -1 coinvariant and degree 0
invariant maps are the ordinary adjunction bijections, so the short exact sequences
give the bijection on full native Hom sets. Transport H, e and d through the closure
and realization identifications. No native right adjoint is used. Empty schemes and
identity compactifications use the same exact comparisons. -/
theorem native_exceptional_left_models (R : Family l D) :
    ∃ model : ∀ T : Space D, ForgetModel D l R T,
      ∀ (X Y : Space D) (f₀ : X.base ⟶ Y.base)
        [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
        (S : CoefficientSystem D l f₀) (c : Compactification (geometricMap D f₀)),
      ∃ a : nativeShriek D l f₀ ⋙ (model Y).functor ≅
          (model X).functor ⋙ (S.ring.operation c .closed).F,
        ∀ L : W D l Y, ∃ (H : W D l X)
          (e : (model X).functor.obj H ≅
            (S.ring.operation c .closed).G.obj ((model Y).functor.obj L))
          (d : (nativeShriek D l f₀).obj H ⟶ L),
          (model Y).functor.map d = a.hom.app H ≫
            (S.ring.operation c .closed).F.map e.hom ≫
            (S.ring.operation c .closed).adjunction.counit.app ((model Y).functor.obj L) ∧
          ∀ K : W D l X,
            Function.Bijective (fun v : K ⟶ H ↦ (nativeShriek D l f₀).map v ≫ d) := by
  sorry

end WeilConjectures.NativeExceptionalForgetful
