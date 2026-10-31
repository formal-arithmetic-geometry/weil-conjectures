/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicModuliStack
public import WeilConjectures.AlgebraicGeometry.DmStackMorphismProperties

/-! # Smooth morphisms of algebraic stacks

Source: Stacks Project, Morphisms of Stacks, Tags 06FM and 075U
(blueprint: def-sfb-smooth-moduli-map).

We use the existential smooth scheme presentation of Tag 06FM(2). The source chart
is surjective; the target chart need only be representable smooth. Smoothness of
representable maps is the existing algebraic-space scheme-test predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- Smoothness by a 2-commutative smooth scheme presentation: the source chart is a
smooth surjective atlas, the target chart is representable smooth, and the map of
schemes is smooth. No representability of the original morphism is required.
Source: Stacks Project, Morphisms of Stacks, Tags 06FM(2) and 075U
(blueprint: def-sfb-smooth-moduli-map). -/
@[no_expose] def IsSmoothModuliMap {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) : Prop :=
  ∃ (U V : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) X)
      (b : BasedFunctor (discreteModuli (yoneda.obj V)) Y) (q : U ⟶ V),
    IsSmoothModuliAtlas X U a ∧ ModuliSpaceTest @Smooth b ∧ Smooth q.left ∧
      Nonempty (a.comp f ≅ (discreteModuliMap (yoneda.map q)).comp b)

/-- The smooth presentation characterizing smoothness of a stack morphism.
Source: Stacks Project, Morphisms of Stacks, Tags 06FM(2) and 075U
(blueprint: def-sfb-smooth-moduli-map).

Proof: unfold IsSmoothModuliMap. Its data are precisely the two scheme charts,
their smooth connecting morphism, and the comparison 2-isomorphism displayed here. -/
theorem isSmoothModuliMap_iff {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) :
    IsSmoothModuliMap f ↔
      ∃ (U V : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) X)
          (b : BasedFunctor (discreteModuli (yoneda.obj V)) Y) (q : U ⟶ V),
        IsSmoothModuliAtlas X U a ∧ ModuliSpaceTest @Smooth b ∧ Smooth q.left ∧
          Nonempty (a.comp f ≅ (discreteModuliMap (yoneda.map q)).comp b) := by
  sorry

end CategoryTheory
