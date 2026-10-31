/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfOpenClosedTriangleData

/-! # Comparison of the ordinary open kernel with recorded compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ordinary exact open kernel on a complete constructible input is the recorded
compact-support value of its completed open pullback. The constructibility of that
pullback is supplied separately; this statement asserts no preservation or linearity.
Source: blueprint localization, integral sheaf sequence and constructibility paragraphs;
Bhatt--Scholze, Lemmas 6.1.13, 6.5.3--6.5.5 and Definition 6.7.6; Stacks 09AH, 099N
(blueprint: lem-sf-integral-open-kernel-compact-support).

Proof: apply ringed open/closed localization with the actual completed coefficient
comparison. The counit of the open adjoint identifies its composite with ordinary
restriction with the kernel of the given closed unit, including the kernel inclusion.
Localize this exact identification termwise. The immersion completed-pullback comparison,
normalized by the completion unit, identifies ordinary restriction of K with the recorded
integral pullback, since K is complete. Exact open extension preserves countable products
and the augmented Roos triangle. The strict open reduction comparison identifies the
resulting tower with the finite compact-support tower for the compactification (j,id),
including all successive quotient maps. Thus the ordinary open value is a derived limit
of that tower. The recorded compact-support value is another vertex of its Roos triangle;
rotate both triangles and use the identity on the two product vertices to obtain the
required isomorphism. This applies equally to zero inputs and empty open complements. -/
theorem sfIntegralOpenKernel_compactSupport
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (K : sfIntegralConstructibleCategory l E X)
    (h : sfIntegralConstructible l E U ((integralDerivedPullback l E j).obj K.obj)) :
    letI := sfRecollementNoetherian k X
    letI := (sfRecollementOpenFiniteType k j).1
    letI := (sfRecollementOpenFiniteType k j).2.1
    letI := (sfRecollementOpenFiniteType k j).2.2
    Nonempty ((sfRecollementModuleOpen l E i).mapDerivedCategory.obj K.obj ≅
      (sfIntegralCompactSupportValue l E k hk
        (Compactification.ofIsOpenImmersion j) ⟨_, h⟩).obj) := by sorry

end WeilConjectures
