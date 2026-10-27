/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource

/-! # Descent through a smooth surjective source cover

Source: Stacks Project, stacks-properties.tex, Tag 06M2;
spaces-descent.tex, Tags 06ET and 06EV
(blueprint: lem-sfb-smooth-cover-flat-lfp-descent).

Flatness and local finite presentation descend separately, without quasi-compactness
of the smooth surjective source cover.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- Flatness and local finite presentation each descend through a smooth surjective
representable map of algebraic stacks.

Source: Stacks Project, Tag 06M2, with Tags 06ET and 06EV
(blueprint: lem-sfb-smooth-cover-flat-lfp-descent).

Proof:
1. For any scheme T mapping to C, put Y = B ×_C T and X = A ×_C T.
Representability of g gives the space Y. Applying
lem-sfb-representable-pullback-over-space to h and Y → B gives the space
X = A ×_B Y. Its projection p : X → Y is smooth and surjective by
lem-sfb-stack-chartwise-smooth-etale-calculus. If h.comp g has the property P
(flatness or, separately, local finite presentation), then X → T has P.
2. Choose a surjective étale scheme chart U → Y and a surjective étale scheme
chart V → X ×_Y U. The induced scheme map v : V → U is smooth and surjective,
hence flat and locally of finite presentation. The composite V → T has P.
Base change and composition are provided by
lem-sfb-stack-chartwise-smooth-etale-calculus; the scheme comparison uses
lem-sfb-space-etale-presentation-property-criterion and
lem-sfb-scheme-etale-source-target-properties. The fibre-product projections
identify V → T with v followed by the induced f : U → T.
3. For flatness, lem-pc-flat-source-descent applied to v and f gives Flat f.
For local finite presentation, apply lem-trf-lfp-fppf-source-locality to the
singleton covering family consisting of v. Its flatness, local finite
presentation and surjectivity give local finite presentation of f. Neither
argument assumes the other property of the composite.
4. The source chart U → Y, the target chart id_T, and f form an étale presentation.
The criterion lem-sfb-space-etale-presentation-property-criterion and locality
lem-sfb-scheme-etale-source-target-properties give P(Y → T). Since T → C was
arbitrary, g has P by its scheme-base-change test. No chart or source cover was
required to be quasi-compact. -/
theorem smooth_cover_flat_lfp_descent
    {S : Scheme.{u}}
    {A : BasedCategory.{v₁, w₁} (Over S)} {B : BasedCategory.{v₂, w₂} (Over S)}
    {C : BasedCategory.{v₃, w₃} (Over S)}
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (hC : IsAlgebraicModuliStack C) (h : BasedFunctor A B) (g : BasedFunctor B C)
    (hh : IsRepresentableByAlgebraicSpaces h) (hg : IsRepresentableByAlgebraicSpaces g)
    (hsmooth : ModuliSpaceTest @Smooth h) (hsurj : IsSurjectiveModuliMap h) :
    (ModuliSpaceTest @Flat (h.comp g) → ModuliSpaceTest @Flat g) ∧
      (ModuliSpaceTest @LocallyOfFinitePresentation (h.comp g) →
        ModuliSpaceTest @LocallyOfFinitePresentation g) := by
  sorry

end CategoryTheory
