/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Artinian.Defs

/-! # Versality at a field-valued point of a fibred groupoid

Source: Stacks Project, artin.tex, Tag 07XF, definition-versal, and
formal-defos.tex, definition-smooth-morphism
(blueprint: def-sfb-pointwise-versal-lifting).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory

/-- The Artinian lifting property at a specified field-valued point. The surjection
`r` identifies the residue field of `A` with `K`; its composite with `q` supplies
that of `A'`. Surjectivity onto a field from a local ring makes the kernel its
unique maximal ideal. No embedding of the residue field into a test ring is assumed.
The base structure `s'` and the over-map `a` impose all algebra compatibilities.

In a category fibred in groupoids, arrows `j` and `z` encode the chosen restriction
of `y'` and its specified isomorphism to `a`-pullback of `x`. The equality `j ≫ t = z`
retains precisely that isomorphism. This uses the existing total category, rather
than choosing a new cleavage or discarding automorphisms.

Source: Stacks Project, artin.tex, Tag 07XF, equation-hat-x and definition-versal;
formal-defos.tex, definition-smooth-morphism
(blueprint: def-sfb-pointwise-versal-lifting). -/
def IsVersalAtField {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    {U : Over S} (x : Functor.Fiber F.p U)
    (K : Type u) [Field K] (α : Spec (.of K) ⟶ U.left) : Prop :=
  ∀ (A' A : CommRingCat.{u}) [IsArtinianRing A'] [IsLocalRing A']
    [IsArtinianRing A] [IsLocalRing A] (q : A' ⟶ A),
    Function.Surjective q.hom →
    ∀ (r : A ⟶ CommRingCat.of K), Function.Surjective r.hom →
    ∀ (s' : Spec A' ⟶ S) (a : Over.mk (Spec.map q ≫ s') ⟶ U),
      Spec.map r ≫ a.left = α →
    ∀ (y' : Functor.Fiber F.p (Over.mk s'))
      (y : Functor.Fiber F.p (Over.mk (Spec.map q ≫ s')))
      (j : y.val ⟶ y'.val) (z : y.val ⟶ x.val),
      F.p.IsHomLift
        (Over.homMk (U := Over.mk (Spec.map q ≫ s')) (V := Over.mk s')
          (Spec.map q) rfl) j → F.p.IsHomLift a z →
      ∃ (b : Over.mk s' ⟶ U) (t : y'.val ⟶ x.val),
        Spec.map q ≫ b.left = a.left ∧ F.p.IsHomLift b t ∧ j ≫ t = z

end CategoryTheory
