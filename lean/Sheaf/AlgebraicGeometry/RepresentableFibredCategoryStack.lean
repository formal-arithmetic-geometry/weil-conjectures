/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf

/-! # Scheme-representable fibred groupoids over an étale stack

Source: Stacks Project, algebraic.tex, Tag 05UN, stack assertion specialized to
scheme representatives and étale coverings; stacks.tex, Tag 0CKJ
(blueprint: lem-sfb-representable-fibred-category-stack).
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A category fibred in groupoids whose scheme base changes over an étale stack
are represented by schemes is itself an étale stack. The equivalences commute
with the projections to the test scheme, up to a 2-isomorphism over `Sch/S`.

Source: Stacks Project, algebraic.tex, Tag 05UN, and stacks.tex, Tag 0CKJ
(blueprint: lem-sfb-representable-fibred-category-stack).

Proof:
1. For a test scheme T and y in G(T), consider the relative groupoid of pairs
(x, theta : q(x) ≅ y). Its arrows a satisfy theta' q(a) = theta. In the
2-fibre product the comparison is theta inverse, giving exactly this equation.
The assumed equivalence identifies its classes with maps to P_T, compatibly
with restriction, and its hom-sets with those of a discrete groupoid. Thus
there is at most one relative arrow. Applying this to (x, q(a)) and (x', id)
shows that q is faithful on fibres. These constructions use
`def-sfb-stable-pointed-moduli-groupoids`.
2. Restrict to the small étale site of T. The arbitrary T-scheme P_T represents
a sheaf there by `lem-weil-pbc-small-etale-representable-presheaf-sheaf`.
The relative isomorphism classes therefore glue uniquely on étale covers
and their overlaps. No étaleness, separatedness or finiteness of P_T is needed.
3. Given compatible local isomorphisms in F, glue their images in G using its
isomorphism sheaves. The two resulting relative pairs have equal classes
locally, hence globally by step 2. Full faithfulness of the equivalence lifts
the identity of their common represented section to an arrow of pairs.
Faithfulness of q proves that it restricts to the prescribed arrows, and
also proves uniqueness. Thus the isomorphisms in F form étale sheaves.
4. Apply q to a descent datum (x_i, phi_ij) in F. Effective descent in G gives
y and theta_i : q(x_i) ≅ y with theta_i q(phi_ij) = theta_j. The relative
classes of (x_i, theta_i) consequently form a matching family.
5. Step 2 glues this family to a section of P_T. Essential surjectivity of the
equivalence gives a relative pair (x, theta), and local arrows alpha_i from
x to x_i with theta_i q(alpha_i) = theta. On overlaps,
theta_i q(phi_ij alpha_j) = theta_j q(alpha_j) = theta = theta_i q(alpha_i).
Cancellation and faithfulness give phi_ij alpha_j = alpha_i. These arrows
effect the original descent datum. Together with step 3 this is precisely
`IsModuliStack F`, as in `def-sfb-stable-pointed-moduli-groupoids`. -/
theorem isModuliStack_of_scheme_representable
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (q : BasedFunctor F G) (hF : IsFibredInGroupoids F) (hG : IsModuliStack G)
    (hq : ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
      ∃ (P : Over S) (p : P ⟶ T)
        (e : BasedFunctor (discreteModuli (yoneda.obj P)) (moduliTwoFiberProduct t q)),
        e.toFunctor.IsEquivalence ∧
          Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst t q))
            (discreteModuliMap (yoneda.map p)))) :
    IsModuliStack F := by
  sorry

end CategoryTheory
