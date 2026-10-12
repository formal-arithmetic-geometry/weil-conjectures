/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# Fibre products commute with inverse limits of schemes

Source: Stacks Project, Categories, Lemma 4.14.10 (Tag 002M), limit clause;
blueprint node `lem-kun-fibre-product-limits` (blueprint: lem-kun-fibre-product-limits).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-kun-fibre-product-limits) For a compatible diagram of cospans of schemes,
the canonical map from the limit of the fibre products to the fibre product of the limits is
an isomorphism (Stacks Project, Categories, Tag 002M, limit clause). A map into the source is
a compatible family of maps into each fibre product. Its components are compatible pairs of
maps into `X` and `Y` with equal composites into `S`. The limit universal properties turn
these into a pair of maps into the limits of `X` and `Y` with equal composites into the limit
of `S`. The target fibre product represents the same pairs, and the comparison acts as the
identity on them, so it is invertible. -/
theorem Scheme.isIso_limit_pullback_comparison
    {J : Type w} [Category.{v} J]
    (X Y S : J ⥤ Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S)
    [HasLimit X] [HasLimit Y] [HasLimit S] [HasLimit (pullback f g)] :
    IsIso (pullback.lift (f := limMap f) (g := limMap g)
      (limMap (pullback.fst f g))
      (limMap (pullback.snd f g)) (by
        apply limit.hom_ext (F := S)
        intro j
        simp only [Category.assoc, limMap_π]
        rw [← Category.assoc, limMap_π, ← Category.assoc, limMap_π]
        simpa only [Category.assoc, NatTrans.comp_app] using
          congrArg (fun a : pullback f g ⟶ S => limit.π (pullback f g) j ≫ a.app j)
            (pullback.condition (f := f) (g := g)))) := by
  classical
  -- Assemble the compatible pairs into a cone over the functor-category pullback.
  let P := pullback (limMap f) (limMap g)
  let a : (Functor.const J).obj P ⟶ X :=
    ((limit.cone X).extend (pullback.fst (limMap f) (limMap g))).π
  let b : (Functor.const J).obj P ⟶ Y :=
    ((limit.cone Y).extend (pullback.snd (limMap f) (limMap g))).π
  have hab : a ≫ f = b ≫ g := by
    ext j
    change pullback.fst (limMap f) (limMap g) ≫ limit.π X j ≫ f.app j =
      pullback.snd (limMap f) (limMap g) ≫ limit.π Y j ≫ g.app j
    rw [← limMap_π, ← limMap_π, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun h ↦ h ≫ limit.π S j) (pullback.condition (f := limMap f) (g := limMap g))
  let c : Cone (pullback f g) := ⟨P, pullback.lift a b hab⟩
  let t := limit.lift (pullback f g) c
  have ht₁ : t ≫ limMap (pullback.fst f g) = pullback.fst (limMap f) (limMap g) := by
    apply limit.hom_ext
    intro j
    simp only [Category.assoc, limMap_π, t, limit.lift_π_assoc]
    change (pullback.lift a b hab).app j ≫ (pullback.fst f g).app j = a.app j
    simpa only [NatTrans.comp_app] using
      congrArg (fun h ↦ h.app j) (pullback.lift_fst a b hab)
  have ht₂ : t ≫ limMap (pullback.snd f g) = pullback.snd (limMap f) (limMap g) := by
    apply limit.hom_ext
    intro j
    simp only [Category.assoc, limMap_π, t, limit.lift_π_assoc]
    change (pullback.lift a b hab).app j ≫ (pullback.snd f g).app j = b.app j
    simpa only [NatTrans.comp_app] using
      congrArg (fun h ↦ h.app j) (pullback.lift_snd a b hab)
  -- The limit and pointwise pullback projections jointly detect the inverse identities.
  refine ⟨⟨t, ?_, ?_⟩⟩
  · apply limit.hom_ext
    intro j
    apply (cancel_mono (pullbackObjIso f g j).hom).1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackObjIso_hom_comp_fst]
      rw [← limMap_π]
      rw [← Category.assoc t, ht₁, pullback.lift_fst_assoc, Category.id_comp]
    · simp only [Category.assoc, pullbackObjIso_hom_comp_snd]
      rw [← limMap_π]
      rw [← Category.assoc t, ht₂, pullback.lift_snd_assoc, Category.id_comp]
  · apply pullback.hom_ext <;> simp [Category.assoc, ht₁, ht₂]

end AlgebraicGeometry
