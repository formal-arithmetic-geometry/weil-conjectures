/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change commutes with a fibre product

Source: Stacks Project, Tag 038F and the fibre-product base-change identifications used in
Tag 054P (blueprint: lem-pc-base-change-product).

The statement records the canonical projection-compatible isomorphism between the base change
of a fibre product of schemes over a field and the fibre product of the two base changed schemes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Base change of a fibre product is canonically the fibre product of the base changes.
Source: Stacks Project, Tag 038F and the fibre-product base-change identifications used in
Tag 054P (blueprint: lem-pc-base-change-product).
Proof: (1) Write `P = X ×_k Y` and `A = P ×_k Spec k'`, with projections `r` and `s`.
The universal property of `X ×_k Spec k'` gives the map with components `(r ≫ fst, s)`;
the corresponding map to `Y ×_k Spec k'` has components `(r ≫ snd, s)`. These maps agree
on their composites to `Spec k'` (def-pc-fibre-product, def-pc-base-change).
For maps from any scheme `T` to the two base changed factors which agree over `Spec k'`,
their components to `X` and `Y` agree over `Spec k`, hence give a unique map `c : T ⟶ P`.
Pair `c` with their common component to `Spec k'` to get a unique map `T ⟶ A`.
The lift equations and hom-extensionality of each pullback verify its two projections
and its uniqueness. Thus `A` is a fibre product of the two base changed factors.
(2) Uniqueness of fibre products now gives the unique isomorphism from `A` to the chosen
fibre product `B`, with the prescribed projections (def-pc-fibre-product).
The common second component is `s`, so the isomorphism is over `Spec k'`. -/
theorem baseChange_product
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (X Y : Scheme.{u})
    (f : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k)))
    (g : Y ⟶ Scheme.Spec.obj (op (CommRingCat.of k))) :
    let i : Scheme.Spec.obj (op (CommRingCat.of k')) ⟶ Scheme.Spec.obj (op (CommRingCat.of k)) :=
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap k k')).op
    let P : Scheme.{u} := pullback f g
    let hP : P ⟶ Scheme.Spec.obj (op (CommRingCat.of k)) := pullback.snd f g ≫ g
    let A : Scheme.{u} := pullback hP i
    let B : Scheme.{u} := pullback (pullback.snd f i) (pullback.snd g i)
    ∃ e : A ≅ B,
      e.hom ≫ pullback.fst (pullback.snd f i) (pullback.snd g i) ≫
          pullback.fst f i =
        pullback.fst hP i ≫ pullback.fst f g ∧
      e.hom ≫ pullback.fst (pullback.snd f i) (pullback.snd g i) ≫
          pullback.snd f i =
        pullback.snd hP i ∧
      e.hom ≫ pullback.snd (pullback.snd f i) (pullback.snd g i) ≫
          pullback.fst g i =
        pullback.fst hP i ≫ pullback.snd f g ∧
      e.hom ≫ pullback.snd (pullback.snd f i) (pullback.snd g i) ≫
          pullback.snd g i =
        pullback.snd hP i := by
  sorry

end AlgebraicGeometry
