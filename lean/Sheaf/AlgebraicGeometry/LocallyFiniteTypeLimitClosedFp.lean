/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Locally finite type schemes as limits of closed finite presentation models

Source: Stacks Project, Limits, Tag 09ZQ, `lemma-finite-type-is-limit-finite-presentation`
(blueprint: lem-weil-pbc-lft-limit-closed-fp).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A qcqs scheme locally of finite type over a quasi-separated base is the inverse limit
of a nonempty directed system of qcqs schemes of finite presentation over that base.
Both the transition maps and the projections from the given scheme are closed immersions.

Source: Stacks Project, Limits, Tag 09ZQ, `lemma-finite-type-is-limit-finite-presentation`
(blueprint: lem-weil-pbc-lft-limit-closed-fp).

Proof:
1. The image of `X` is quasi-compact. Cover it by finitely many affine opens in `S` and
   let `S₀` be their union. It is qcqs, and `f` factors through it by a locally finite type
   morphism. The qcqs morphism permanence lemma gives quasi-compactness and
   quasi-separatedness of this factor. If `X` is empty, take `S₀` empty.
2. Over `S₀`, use the Nagata finite type finite presentation model system and its property
   theorem (`def-nagata-finite-type-fp-model-system` and
   `lemma-nagata-finite-type-fp-model-system`). The finite type quasi-coherent subideals of
   the defining ideal form a nonempty directed set: zero belongs to it and sums give upper
   bounds (`def-nagata-closed-subscheme-fp-system`). Its models have finite presentation,
   its transitions and projections are closed immersions, and its cone with point `X` is
   limiting. The qcqs morphism permanence lemma shows that all the models are qcqs.
3. The open inclusion `S₀ ⟶ S` is locally of finite presentation, quasi-compact and
   quasi-separated, hence of finite presentation. Compose the model structure maps with
   this inclusion, using finite presentation permanence. The diagram, its projections and
   its limit property in schemes stay the same, and their composites to `S` equal `f`. -/
theorem exists_locallyFiniteType_limit_closed_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiSeparatedSpace S] [LocallyOfFiniteType f]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (I : Type u) (_ : Preorder I),
      Nonempty I ∧ IsDirected I (· ≤ ·) ∧
      ∃ (D : Iᵒᵖ ⥤ Scheme.{u}) (p : D ⟶ (Functor.const Iᵒᵖ).obj S)
        (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i : Iᵒᵖ, LocallyOfFinitePresentation (p.app i) ∧
          QuasiCompact (p.app i) ∧ QuasiSeparated (p.app i)) ∧
        (∀ i : Iᵒᵖ, CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i)) ∧
        (∀ (i j : Iᵒᵖ) (g : i ⟶ j), IsClosedImmersion (D.map g)) ∧
        (∀ i : Iᵒᵖ, π.app i ≫ p.app i = f) ∧
        Nonempty (IsLimit (Cone.mk X π)) ∧
        (∀ i : Iᵒᵖ, IsClosedImmersion (π.app i)) := by
  sorry

end AlgebraicGeometry
