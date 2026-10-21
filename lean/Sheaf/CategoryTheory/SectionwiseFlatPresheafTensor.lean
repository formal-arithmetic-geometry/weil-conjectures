/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Tensoring with a sectionwise flat module presheaf

Source: Stacks Project, Modules on Sites, Tags 03ES and 03ER(1)
(blueprint: lem-weil-pbc-sectionwise-flat-presheaf-tensor).
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace PresheafOfModules

/-- Tensoring on the right with a sectionwise flat module presheaf preserves finite limits,
with the canonical kernel and finite-product comparisons. The kernel isomorphism is
characterized by its compatibility with the kernel inclusions; this equation uniquely
specifies its forward map. The product comparison is induced by the projections.
All maps here are morphisms of module presheaves, hence commute with semilinear restrictions.

Source: Stacks Project, Modules on Sites, Tag 03ES (lemma-flatness-presheaves) and
Tag 03ER(1) (definition-flat)
(blueprint: lem-weil-pbc-sectionwise-flat-presheaf-tensor).

Proof:
1. The tensor presheaf and its action on morphisms are the sectionwise tensor constructions
of [def-pur-presheaf-tensor-product]. On pure tensors, restriction sends `a ⊗ p` to
`r_A(a) ⊗ r_P(p)`. Semilinearity respects balancing over the restriction of the ring.
Naturality, identities, composition and additivity follow on pure tensors and hence on
all tensors, since pure tensors generate.
2. Compute the kernel of `f` sectionwise as the submodule of sections killed by `f`.
Naturality of `f` induces its restrictions. The sectionwise unique factorizations through
this submodule are natural, so give the categorical kernel of module presheaves.
3. Compute products sectionwise, with coordinatewise restrictions. Their projections and
tuple factorizations are natural and linear, giving the categorical product. The empty
product is the zero module presheaf.
4. Apply [lem-weil-pbc-flat-tensor-exact] at each object to the exact sequence starting
with the kernel inclusion. Flatness gives an injective tensored inclusion with image
exactly the kernel of the tensored map, hence the stated sectionwise isomorphism.
5. Both composites of restriction with this comparison have the same image under the
kernel inclusion: on a pure tensor they give `r_A(i(k)) ⊗ r_P(p)`. Injectivity of the
inclusion and generation by pure tensors prove naturality. The component inverses are
natural by multiplying this naturality identity by the inverses. This gives the kernel
isomorphism with the asserted inclusion equation.
6. Apply [lem-weil-pbc-tensor-finite-product] sectionwise, using a fixed enumeration of
the finite family. The projection comparison sends `(a_i) ⊗ p` to `(a_i ⊗ p)` and commutes
with restrictions on pure tensors. Its component inverses are natural by the same inverse
identity as in step 5. For the empty family both sides are zero.
7. Any finite diagram has limit the kernel of the difference map from the product over
its objects to the product over its arrows. The arrow component is the diagram map after
the source projection minus the target projection. The kernel equations are exactly the
cone equations. Additivity identifies the tensored difference map, through the product
comparisons, with the difference map of the tensored diagram. Steps 4--6 therefore give
the canonical limit comparison, compatibly with all cone projections. This includes the
empty diagram and proves preservation of finite limits. -/
theorem tensorRight_preservesFiniteLimits_of_sectionwise_flat
    {C : Type u} [Category.{v} C] (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (R : Sheaf J.toGrothendieck CommRingCat.{w})
    (P : PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (hP : ∀ V : Cᵒᵖ, Module.Flat (R.obj.obj V) (P.obj V)) :
    PreservesFiniteLimits (tensorRight P) ∧
      (∀ (A B : PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat)) (f : A ⟶ B),
        ∃ e : (tensorRight P).obj (kernel f) ≅ kernel ((tensorRight P).map f),
          e.hom ≫ kernel.ι ((tensorRight P).map f) = (tensorRight P).map (kernel.ι f)) ∧
      (∀ (I : Type t) [Finite I]
        (A : I → PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat)),
        IsIso (piComparison (tensorRight P) A)) := by
  sorry

end PresheafOfModules
