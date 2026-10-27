/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.CategoryTheory.VaryingSiteSystem

/-!
# Componentwise abelian structure on coherent varying-site systems

Source: Stacks Project, sites-cohomology.tex, Tag 0EXZ, system category;
agent generalization to arbitrary small coherent diagrams.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The system category is abelian, and evaluation is additive
and exact. A kernel fork or cokernel cofork is universal precisely when every
component is universal.

Source: Stacks Project, sites-cohomology.tex, Tag 0EXZ, system category and product
construction; componentwise abelian-category argument, generalized by an agent
(blueprint: lem-per-varying-site-system-abelian-componentwise).

Proof: Give compatible morphism families their componentwise abelian group structure;
additivity of each inverse image makes the compatibility equations closed under
addition and negation. Construct finite biproducts componentwise; their system
laws follow from their projections and the additivity of inverse image.
For a morphism take componentwise kernels. Exactness of inverse
image identifies the inverse image of a kernel with the kernel of the inverse-image
map, and hence defines its transition by the kernel universal property. Cancel
kernel inclusions to check all system laws and the factorization of any compatible
family. Dually, inverse image is a left adjoint and preserves cokernels; define
cokernel transitions by descent and cancel the epic projections. These constructions
also show the two stated equivalences of universal properties. Finite biproducts
are componentwise. Image and coimage are consequently componentwise, and their
comparison is an isomorphism because it is so at each vertex: component inverses
satisfy compatibility by composing the original square with inverses. Thus the
category is abelian. Evaluation preserves kernels, cokernels, finite biproducts
and the zero object, hence finite limits and finite colimits. All constructions
work for empty index sets and for noninvertible transition maps. -/
theorem varyingSiteSystem_abelian_componentwise
    {I : Type u} [SmallCategory I] (D : VaryingSiteDiagram.{u} I)
    (e : VaryingSiteCoherence D) :
    ∃ (_ : Abelian (VaryingSiteSystem D e)),
      ∃ (_ : ∀ i : I, (VaryingSiteSystem.evaluation D e i).Additive),
        (∀ i : I,
          PreservesFiniteLimits (VaryingSiteSystem.evaluation D e i) ∧
          PreservesFiniteColimits (VaryingSiteSystem.evaluation D e i)) ∧
        (∀ (F G : VaryingSiteSystem D e) (h : F ⟶ G) (c : KernelFork h),
          Nonempty (IsLimit c) ↔ ∀ i : I,
            Nonempty (IsLimit ((VaryingSiteSystem.evaluation D e i).mapCone c))) ∧
        (∀ (F G : VaryingSiteSystem D e) (h : F ⟶ G) (c : CokernelCofork h),
          Nonempty (IsColimit c) ↔ ∀ i : I,
            Nonempty (IsColimit ((VaryingSiteSystem.evaluation D e i).mapCocone c))) := by
  sorry

end CategoryTheory
