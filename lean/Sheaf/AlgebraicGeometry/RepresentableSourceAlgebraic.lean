/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-! # Algebraicity of a representable source

Source: Stacks Project, algebraic.tex, Tags 05UN and 05UM; stacks-morphisms.tex,
Tags 06Q2 and 06Q3 (blueprint: lem-sfb-stack-representable-source-algebraic).

The source is initially only fibred in groupoids. Local finite presentation over
`S` is expressed by a smooth scheme atlas whose structural map is locally of finite
presentation. The relative hypothesis retains the projection of each space base change.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A fibred groupoid representable by algebraic spaces over an algebraic stack is
algebraic. If the scheme base changes are locally of finite presentation on étale
charts and the target has a smooth atlas locally of finite presentation over the
base, the source has such an atlas as well.

Source: Stacks Project, algebraic.tex, Tags 05UN and 05UM; stacks-morphisms.tex,
Tags 06Q2 and 06Q3 (blueprint: lem-sfb-stack-representable-source-algebraic).

Proof:
1. Representability kills relative automorphisms, making the fibre functors faithful.
For an object y of the target, the presheaf of classes of pairs (x, y ≅ j(x)) is
represented by its space base change. It is an fppf sheaf and therefore an étale
sheaf, using def-sfb-stable-pointed-moduli-groupoids, def-trf-algebraic-space,
def-pc-fppf-site and def-weil-etale-morphism.
2. The target is an étale stack. Apply lem-sfb-relative-sheaf-fibred-descent to the
faithful map and these relative sheaves, obtaining descent in the source.
3. For two source objects over T, their target Isom space B is algebraic. Over a
scheme H mapping to B, lift the given target isomorphism to a pair of sections of
H ×_Y X. Their equalizer is represented by a scheme via the space diagonal.
Its points are exactly source isomorphisms mapping to the specified target
isomorphism, uniquely by faithfulness. Apply lem-sfb-presheaf-space-target-bootstrap
to obtain the source Isom algebraic space. This proves the diagonal condition,
using def-trf-scheme-algebraic-space and the preceding definitions.
4. Pull back a smooth surjective scheme atlas V → Y to an algebraic space A over
X. Refine A by an étale surjective scheme chart U → A. By
lem-sfb-fibred-groupoid-representable-smooth-calculus, U → X is representable,
smooth and surjective. The preceding descent and diagonal results give
IsAlgebraicModuliStack X by def-sfb-algebraic-moduli-stack.
5. Under the additional hypotheses choose V → Y with V → S locally of finite
presentation. Choose the base-change presentation over V with the stated chart
property, and its étale chart U. Then U → V is locally of finite presentation.
Compose with V → S using lem-sbc-locally-finite-presentation-composition and
def-sbc-locally-finite-presentation. The same atlas U → X proves the last clause. -/
theorem isAlgebraicModuliStack_of_representable
    {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (j : BasedFunctor X Y) (hX : IsFibredInGroupoids X)
    (hY : IsAlgebraicModuliStack Y) (hj : IsRepresentableByAlgebraicSpaces j) :
    IsAlgebraicModuliStack X ∧
      ((∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
          ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
            HasSpaceBaseChange j T t Z p ∧
              ∀ (U : Over S) (b : yoneda.obj U ⟶ Z.obj.obj),
                AlgebraicSpace.IsEtale b →
                  LocallyOfFinitePresentation ((yoneda.preimage (b ≫ p)).left)) →
        (∃ (V : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj V)) Y),
          IsSmoothModuliAtlas Y V a ∧ LocallyOfFinitePresentation V.hom) →
        ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) X),
          IsSmoothModuliAtlas X U a ∧ LocallyOfFinitePresentation U.hom) := by
  sorry

end CategoryTheory
