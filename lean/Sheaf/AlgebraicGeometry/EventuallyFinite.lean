/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.EventuallyAffine
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Eventually finite stages in an inverse system

Source: Stacks Project, Limits, Lemma 09ZN, `lemma-eventually-finite`
(blueprint: lem-weil-pbc-eventually-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An inverse system of qcqs schemes over a qcqs base, with finite transitions and
locally finite type structure maps, has eventually finite structure maps if its limit
structure map is integral.

Source: Stacks Project, Limits, Lemma 09ZN, `lemma-eventually-finite`.
(blueprint: lem-weil-pbc-eventually-finite)

Proof plan:
1. Integral morphisms and finite transitions are affine
   (def-weil-finite-integral-morphism). Apply `eventually_affine`
   (lem-weil-pbc-eventually-affine). Restrict to the resulting cofinal upper tail,
   which has the same limit by directedness.
2. Choose a finite affine open cover of the base (def-pc-scheme). On that tail all
   inverse images are affine (pqf-def-affine-morphism). The open-restriction and
   affine comparison clauses of `exists_limit_affine_transition`
   (lem-weil-pbc-limit-affine-transition) identify their limit with the spectrum of
   the filtered colimit of their rings. The stage algebras are finite type
   (lem-weil-pbc-lft-affine-pairs); transitions are finite and the colimit is integral
   over the base ring (def-weil-finite-integral-morphism).
3. Choose finitely many algebra generators at one stage. Their images in the
   colimit satisfy monic equations by integrality.
4. Descend these finitely many equations to one later stage using equality in a
   filtered ring colimit (lem-pc-filtered-colimit-commrings-elementwise), then take
   a common upper bound of the finitely many indices by directedness.
5. The image of the initial algebra at this stage is finite over the base ring,
   since its finitely many algebra generators are integral
   (lem-weil-pbc-finite-of-integral-generators).
6. The later algebra is finite over that image: its module generators over the
   initial algebra still generate over the image. Products of module generators
   show it is finite over the base ring.
7. Take a common upper bound of the stages chosen for each affine open. Finite
   transitions remain finite on these opens (lem-weil-pbc-finite-local-on-target),
   and composition is finite (lem-weil-pbc-finite-composition). Finiteness is local
   on the target (lem-weil-pbc-finite-local-on-target), giving every later stage.
   For an empty base use the empty cover and choose any index. -/
theorem eventually_finite
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsFinite (D.map g)]
    (h : D ⟶ (Functor.const Iᵒᵖ).obj S)
    [∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)]
    (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ S)
    (_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f) [IsIntegralHom f] :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsFinite (h.app (op i)) := by
  sorry

end AlgebraicGeometry
