/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Affine smooth atlases for finite-type algebraic stacks

Source: Stacks Project, stacks-properties.tex, Tag 04YC (lemma-quasi-compact-stack);
stacks-morphisms.tex, Tags 06FS (definition-locally-finite-type) and 075U
(definition-smooth) (blueprint: lem-sfb-finite-type-stack-affine-smooth-atlas).

Quasi-compactness is stated through finite subcovers of full open substacks, using
scheme-test covering. Local finite type is tested on all smooth scheme atlases.
The same affine finite-type atlas is smooth over the field when the stack is smooth.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- A finite-type algebraic stack over a field has an affine finite-type smooth
surjective atlas, smooth over the field if the stack is smooth.
Source: Stacks Project, Tag 04YC (lemma-quasi-compact-stack), with Tags 06FS and 075U
(blueprint: lem-sfb-finite-type-stack-affine-smooth-atlas).

Proof:
1. Choose a smooth surjective scheme atlas U by def-sfb-algebraic-moduli-stack.
The local-finite-type hypothesis and def-weil-finite-type-morphism give an affine
open cover U_i = Spec B_i, with each B_i finitely generated over k. By
lem-sfb-smooth-atlas-open-image, each restricted atlas has an open image W_i and
is a representable smooth surjection onto W_i.
2. These W_i cover on every scheme test: the base-changed U_i cover the
base-changed atlas, which surjects onto that test scheme. The assumed finite
open-subcover condition gives finitely many W_j still covering the stack.
3. Form the finite scheme coproduct A of the corresponding U_j using
lem-weil-pbc-scheme-coproduct-family. Etale descent of objects from
def-sfb-stable-pointed-moduli-groupoids glues their maps to the stack: self-overlaps
have identity comparisons and distinct overlaps are empty. By
lem-weil-pbc-finite-affine-coproduct-spectrum this coproduct is Spec of the finite
product of the B_j. It is affine and finite type by def-weil-finite-type-morphism.
4. Representability of A to the stack follows from the representable diagonal:
its scheme base changes are the diagonal's base changes along products of scheme
maps (def-pc-fibre-product). Source-open locality in
lem-sfb-stack-chartwise-smooth-etale-calculus gives smoothness from the U_j.
On each scheme test the images are the opens W_j from step 1; they cover by step 2,
so the base-changed map is surjective. Thus this is IsSmoothModuliAtlas.
5. When the stack is smooth over k, its smooth-atlas test says A is smooth over k.
For the empty stack use the empty finite family. Its coproduct is Spec of the zero
ring, allowed by lem-weil-pbc-finite-affine-coproduct-spectrum; finite type and
smoothness also include this empty case. -/
theorem finiteType_stack_affine_smooth_atlas
    (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F)
    (hlft : ∀ (U : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a → LocallyOfFiniteType U.hom)
    (hqc : ∀ C : Set (OpenModuliSubstack F),
      IsOpenModuliCover (fun W : C ↦ W.val) →
      ∃ D : Set (OpenModuliSubstack F), D.Finite ∧ D ⊆ C ∧
        IsOpenModuliCover (fun W : D ↦ W.val)) :
    ∃ (A : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj A)) F),
      IsAffine A.left ∧ LocallyOfFiniteType A.hom ∧ QuasiCompact A.hom ∧
        IsSmoothModuliAtlas F A a ∧ (IsSmoothModuliStack F → Smooth A.hom) := by
  sorry

end CategoryTheory
