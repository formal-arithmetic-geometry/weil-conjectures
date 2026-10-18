/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations

/-!
# Composition of pro-etale module inverse images with constant coefficients

Source: literature/stacks-project/sites-modules.tex, Tag 03D8,
lemma-push-pull-composition-modules (blueprint: lem-pur-proetale-module-pullback-composition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/--
For composable morphisms of schemes and a finite commutative constant coefficient ring, the
module inverse image for the composite is canonically isomorphic to the successive inverse
images. The canonical comparison is the conjugate of the fibre-product direct-image
identification, with the normalized module adjunctions and the prescribed constant-section
actions.

Source: literature/stacks-project/sites-modules.tex, Tag 03D8,
lemma-push-pull-composition-modules (blueprint: lem-pur-proetale-module-pullback-composition).
Proof: for an object of the pro-etale site of the target, the two iterated fibre products and
the fibre product for the composite are canonically isomorphic by the universal property of
scheme fibre products. Restriction along these isomorphisms gives a natural direct-image
isomorphism; naturality also shows that it preserves the canonical constant sections, hence
its module actions. The module inverse images are left adjoint to the direct images by the
normalized module adjunctions. The adjunction conjugation bijection therefore supplies the
unique inverse-image isomorphism whose conjugate is that direct-image comparison.
-/
theorem proEtaleConstantRingModulePullbackComposition
    {X Y Z : Scheme.{u}} (g : Z ⟶ X) (f : X ⟶ Y)
    (Λ : Type u) [CommRing Λ] [Finite Λ] :
    ∃ (a : proEtaleConstantRingPullback Λ (g ≫ f) ≅
        proEtaleConstantRingPullback Λ f ⋙ proEtaleConstantRingPullback Λ g),
      ∃ (d : proEtaleConstantRingPushforward Λ g ⋙
          proEtaleConstantRingPushforward Λ f ≅
          proEtaleConstantRingPushforward Λ (g ≫ f)),
        (∀ (N : proEtaleRingModules Z (proEtaleConstantRing Z Λ))
            (U : Y.ProEt)
            (m : ((proEtaleConstantRingPushforward Λ g ⋙
              proEtaleConstantRingPushforward Λ f).obj N).val.obj (Opposite.op U)),
          (d.hom.app N).val.app (Opposite.op U) m =
            N.val.map ((MorphismProperty.Over.pullbackComp g f).hom.app U).op m) ∧
        conjugateIsoEquiv
            ((proEtaleConstantRingAdjunction Λ f).comp
              (proEtaleConstantRingAdjunction Λ g))
            (proEtaleConstantRingAdjunction Λ (g ≫ f)) a = d := by
  sorry

end AlgebraicGeometry.Scheme
