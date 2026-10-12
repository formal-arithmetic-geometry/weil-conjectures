/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.RingTheory.FiniteMapColimitDescent

/-!
# Local finiteness descent over one affine target open

Source: Stacks Project, Limits, proof of Lemma 01ZO, and Algebra, Lemma 07RG
(blueprint: lem-weil-pbc-descend-finite-affine-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Finiteness on one affine target open descends once an affine stage is known.

Source: Stacks Project, Limits, proof of Lemma 01ZO (affine reduction), and Algebra,
Lemma 07RG (blueprint: lem-weil-pbc-descend-finite-affine-open).

Proof:
1. The inverse image of `V` at stage `k` is affine: the projection to the original
   target is a base change of an affine transition. Its inverse image under `f_k`
   is affine by `haffine`. Pasting identifies later restrictions with base changes
   of this affine morphism; it is locally of finite type by base-change stability.
2. Cover `V` by finitely many affine opens mapping into affine opens of `S₀`.
   This is possible by the affine-open basis and quasi-compactness of `V`.
   Pull them back to stage `k`. The corresponding source, target and base opens
   are affine, and the source coordinate ring is a finite type target algebra.
3. On each base open use the upper tail above `k`. Its limit is the inverse image
   of that open in `c.pt`, and its coordinate ring is the directed colimit of the
   stage coordinate rings, by affine-transition limits and the Spec adjunction.
4. Open pullback pasting and the affine-spectrum pullback isomorphism identify each
   restricted morphism with Spec of the base-changed finite type ring map.
   The hypothesis `hfinite` makes that map finite over the colimit; transport its
   module generators through the coordinate ring isomorphisms.
5. Apply Algebra 07RG to each piece. Finiteness persists at larger indices because
   the images of finitely many module generators generate after scalar extension.
   Directedness supplies one upper bound for these finitely many indices and `k`.
6. At every index above this bound the finite restrictions cover the inverse image
   of `V`. Finiteness is local on the target, so the restriction to that inverse
   image is finite. For an empty cover use `k`; the empty restriction is finite.
-/
theorem exists_isFinite_morphismRestrict_baseChange_affine_open
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ k : I) (hk : i₀ ≤ k)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFiniteType f₀.left]
    (haffine : IsAffineHom (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left))
    (V : Y₀.left.Opens) (hV : IsAffineOpen V)
    (hfinite : IsFinite
      ((((Over.pullback (c.π.app (op i₀))).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (c.π.app (op i₀))) ⁻¹ᵁ V))) :
    ∃ (j : I) (hkj : k ≤ j), ∀ (i : I) (hji : j ≤ i),
      IsFinite
        ((((Over.pullback (D.map (homOfLE (hk.trans (hkj.trans hji))).op)).map f₀).left)
          ∣_ ((pullback.fst Y₀.hom
            (D.map (homOfLE (hk.trans (hkj.trans hji))).op)) ⁻¹ᵁ V)) := by sorry

end AlgebraicGeometry
