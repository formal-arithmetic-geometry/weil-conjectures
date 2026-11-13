/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Constant stalks of étale sheaves on the spectrum of an algebraically closed field

For an algebraically closed field `Ω`, the stalk of an étale sheaf on `Spec Ω` at the identity
geometric point is computed by its global sections.

## References

* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The identity geometric stalk is computed by the global sections map in the
algebraically closed case. -/
theorem spec_algClosed_etale_sheaf_constant_stalk
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf ((Spec (CommRingCat.of Ω)).smallEtaleTopology) (Type (u + 1))) :
    Function.Bijective
      ((pointSmallEtale (𝟙 (Spec (CommRingCat.of Ω)))).toPresheafFiber
        (Etale.mk (𝟙 (Spec (CommRingCat.of Ω))))
        (Over.homMk (𝟙 (Spec (CommRingCat.of Ω)))
          (Category.comp_id (𝟙 (Spec (CommRingCat.of Ω))))) G.obj) := by
  let Φ := pointSmallEtale (𝟙 (Spec (CommRingCat.of Ω)))
  let I := Etale.mk (𝟙 (Spec (CommRingCat.of Ω)))
  let xI : Φ.fiber.obj I := Over.homMk (𝟙 _) (Category.comp_id _)
  have hsec (X : (Spec (CommRingCat.of Ω)).Etale) (x : Φ.fiber.obj X) :
      ∃ g : I ⟶ X, Φ.fiber.map g xI = x := by
    refine ⟨MorphismProperty.Over.homMk x.left x.w, ?_⟩
    apply Over.OverMorphism.ext
    change (𝟙 _) ≫ x.left = x.left
    simp
  constructor
  · intro a b hab
    obtain ⟨Y, f, y, _, heq⟩ := (Φ.toPresheafFiber_eq_iff' (P := G.obj) _ xI a b).mp hab
    obtain ⟨g, _⟩ := hsec Y y
    have hgf : g ≫ f = 𝟙 I := by
      apply MorphismProperty.Over.Hom.ext
      have hf := (g ≫ f).w
      change (g ≫ f).left ≫ 𝟙 _ = 𝟙 _ at hf
      change (g ≫ f).left = 𝟙 _
      simpa using hf
    have h := congrArg (G.obj.map g.op) heq
    simpa [← types_comp_apply, ← Functor.map_comp, ← op_comp, hgf] using h
  · intro z
    obtain ⟨X, x, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := G.obj) z
    obtain ⟨f, hf⟩ := hsec X x
    refine ⟨G.obj.map f.op a, ?_⟩
    change Φ.toPresheafFiber I xI G.obj (G.obj.map f.op a) = _
    rw [Φ.toPresheafFiber_w_apply, hf]

end AlgebraicGeometry.Scheme
