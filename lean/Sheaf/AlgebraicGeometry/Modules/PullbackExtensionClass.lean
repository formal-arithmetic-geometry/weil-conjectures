/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import Sheaf.AlgebraicGeometry.Modules.ExtYonedaFunctoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Yoneda class of a pulled-back extension

Source: Stacks Project, Homology, Tag 010I; Derived Categories, Tag 06XP
(blueprint: lem-sc-p1-pullback-extension-class).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling back an extension along a morphism to its quotient precomposes its Yoneda class.
The middle object is the fiber product, the quotient map is its second projection, and
`j` is the unique inclusion with first projection `S.f` and second projection zero.
Source: Stacks Project, Homology, Tag 010I; Derived Categories, Tag 06XP.
(blueprint: lem-sc-p1-pullback-extension-class)

Proof: (1) Form `P = E ×_C C'`. The inclusion sends `a` to `(i(a), 0)`, and the
quotient map is the second projection. On stalks, this projection is surjective because
`E → C` is surjective; its kernel is exactly the pairs `(i(a), 0)` since `i` identifies
`A` with the kernel of `E → C`. Thus the pullback sequence is short exact. The maps
`(𝟙 A, pullback.fst, u)` give a morphism to the original short exact sequence, by the
fiber-product equation. (2) Apply lem-sc-p1-ext-class-naturality, namely Mathlib's
`ShortComplex.ShortExact.extClass_naturality`, to this morphism. It identifies the
pullback class, postcomposed with the identity on `A`, with the original class
precomposed with `u`; the identity composition leaves the class unchanged.
(3) The first clause of `ext_yoneda_functoriality`
(lem-sc-p1-ext-yoneda-functoriality) identifies this degree-zero Yoneda composition
with the contravariant Ext map. This is the asserted formula `δ ∘ u`. -/
theorem pullback_extClass_precompose {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {C' : X.Modules} (u : C' ⟶ S.X₃) :
    ∃ j : S.X₁ ⟶ Limits.pullback S.g u, ∃ hz : j ≫ pullback.snd S.g u = 0,
      j ≫ pullback.fst S.g u = S.f ∧
      ∃ hp : (ShortComplex.mk j (pullback.snd S.g u) hz).ShortExact,
        (hp.extClass : Ext C' S.X₁ 1) =
          (Abelian.Ext.mk₀ u).comp hS.extClass (zero_add 1) := sorry

end AlgebraicGeometry.Scheme.Modules
