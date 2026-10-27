/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Properness tested on an fppf scheme cover of a stack target

Source: Stacks Project, stacks-properties.tex, Tag 04XD, lemma-check-property-covering,
for properness in Section 04XB
(blueprint: lem-sfb-representable-proper-fppf-target-test).

Properness below is tested on the actual algebraic-space projections of scheme
2-base changes. It includes separatedness, finite type and universal closedness.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- A representable map of algebraic stacks is proper exactly when its pullback
along a surjective flat locally finitely presented scheme cover of the target is proper.
Source: Stacks Project, stacks-properties.tex, Tag 04XD, lemma-check-property-covering,
for properness in Section 04XB
(blueprint: lem-sfb-representable-proper-fppf-target-test).

Proof:
1. If f is proper, test its defining scheme-base-change property at p : W → Y.
   Every further scheme base change of this projection is proper by
   lem-sfb-space-proper-base-change, giving the right-hand scheme-test property.
2. Conversely, for t : T → Y put A = X ×_Y T and B = W ×_Y T. Representability
   makes both algebraic spaces. Choose a surjective etale scheme atlas U → B
   using def-trf-algebraic-space. Its projections give h : U → T, w : U → W,
   and an isomorphism beta : p(w) ≅ t(h), by def-sfb-stable-pointed-moduli-groupoids.
3. The scheme test of p makes B → T surjective, flat and locally finitely presented.
   By lem-sfb-fibred-groupoid-representable-smooth-calculus and
   lem-sfb-stack-chartwise-smooth-etale-calculus the etale atlas is smooth, flat
   and locally finitely presented, and the composite h has these last two
   properties and is surjective. Thus {h} is an fppf covering by def-pc-fppf-site;
   no quasi-compactness of p or its base changes is required.
4. The triple description of the 2-fibre product identifies A ×_T U with
   (X ×_Y W) ×_W U over U: compose the comparison f(x) ≅ t(h(u)) with
   beta(u) inverse to obtain f(x) ≅ p(w(u)), and compose with beta(u) for the
   inverse operation. These operations preserve compatible arrows and pullbacks.
   By lem-trf-space-fibre-products-etale-covers these are algebraic spaces,
   and their discrete fibred groupoids identify the spaces themselves.
5. The assumed proper scheme tests of X ×_Y W → W give properness over U.
   Equivalently use lem-sfb-space-proper-base-change on its proper projection.
   Step 4 identifies this with A ×_T U → U. The properness clause of
   lem-sfb-space-flat-proper-fp-locality descends it along {h} to A → T.
   Since t was arbitrary, all scheme tests of f are proper. -/
theorem representable_proper_fppf_target_test {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (hX : IsAlgebraicModuliStack X) (hY : IsAlgebraicModuliStack Y)
    (f : BasedFunctor X Y) (hf : IsRepresentableByAlgebraicSpaces f)
    (W : Over S) (p : BasedFunctor (discreteModuli (yoneda.obj W)) Y)
    (hp : IsRepresentableByAlgebraicSpaces p)
    (hs : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
      ∃ (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange p T t Z a ∧ SpaceMapIsSurjective Z T a)
    (hflat : ModuliSpaceTest @Flat p)
    (hlfp : ModuliSpaceTest @LocallyOfFinitePresentation p) :
    (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
      ∃ (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange f T t Z a ∧
          MapIsProper (ObjectProperty.homMk ⟨a⟩ : Z ⟶ schemeSpace T)) ↔
    (∀ (T : Over S)
        (t : BasedFunctor (discreteModuli (yoneda.obj T)) (discreteModuli (yoneda.obj W))),
      ∃ (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (moduliTwoFiberFst p f) T t Z a ∧
          MapIsProper (ObjectProperty.homMk ⟨a⟩ : Z ⟶ schemeSpace T)) := by
  sorry

end CategoryTheory
