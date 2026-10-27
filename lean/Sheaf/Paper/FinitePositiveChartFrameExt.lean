/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.FiniteSignedTwistProducts

/-! # Extensionality on compatible ordered frames

Source: finite-reduction proof Step 2, local rank-one gluing, expanded Step 8.
(blueprint: lem-pur-finite-positive-chart-frame-ext)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

/-- Maps from one positive line are determined by compatible ordered frame vectors.
The target is an arbitrary coefficient sheaf; neither map is required to be invertible.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, local invertible twists and
Step 3, rank-one gluing; expanded Step 8 of the root-chart construction.
(blueprint: lem-pur-finite-positive-chart-frame-ext).
Proof: the inverse first chart takes coefficient one to a generator of the first
line. On a trivializing pro-etale cover extend this generator to the coherent
signed frame: take coefficient one at zero, ordered tensor powers in positive
degrees, and the evaluation-dual bases in negative degrees. The scalar realization
unit and its counit identify the ordinary and intrinsic section modules, so these
frames have ordinary representatives satisfying the two heterogeneous equalities.
The assumed equality therefore gives equality of the two maps on the degree-d
basis generator. Both maps are linear over the constant coefficient sheaf, hence
agree on every local section, since every section is a multiple of the basis.
Their values on an arbitrary section agree after restriction to this cover; the
target sheaf's separatedness gives equality before restriction. Sheaf morphism
extensionality proves the claim. At degree zero the same argument uses the unit
basis, and on the empty scheme separatedness gives the unique map. -/
theorem finiteTensorPositiveChart_frame_ext (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
    (e₁ : P.finiteTensorFixedSheaf T 1 ≅
      𝟙_ (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))
    (d : ℕ) (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
    (f g : P.finiteTensorFixedSheaf T d ⟶ M)
    (h : ∀ (V : T.ProEt) (b : P.FiniteTensorFrame T V)
      (x₁ : (P.finiteTensorFixedSheaf T 1).obj.obj (Opposite.op V))
      (x : (P.finiteTensorFixedSheaf T d).obj.obj (Opposite.op V)),
      HEq (P.finiteTensorSection T 1 V x₁) (P.finiteTensorFrameBasis T V b 1) →
      e₁.hom.hom.app (Opposite.op V) x₁ =
        (Functor.LaxMonoidal.ε (sheafToPresheaf (ProEt.topology T)
          (ModuleCat.{u + 1} P.Coefficient))).app (Opposite.op V) (1 : P.Coefficient) →
      HEq (P.finiteTensorSection T d V x) (P.finiteTensorFrameBasis T V b d) →
      f.hom.app (Opposite.op V) x = g.hom.app (Opposite.op V) x) : f = g := by
  sorry

end WeilConjectures.PurityFiniteSetting
