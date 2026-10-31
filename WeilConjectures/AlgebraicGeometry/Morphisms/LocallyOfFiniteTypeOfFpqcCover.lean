/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fpqc descent of local finite type

Source: Stacks Project, Descent, Lemma 02KX, the descent direction of Definition 02KO
(blueprint: lem-weil-pbc-fpqc-descend-locally-finite-type).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-fpqc-descend-locally-finite-type) Stacks Project, Descent,
Lemma 02KX: if every base change along an fpqc covering is locally of finite type, so is `f`.

Proof: apply the fpqc-local-on-base criterion (02KP). Local finite type is Zariski
local on the target and stable under base change. For the affine descent condition,
a morphism between affine schemes is quasi-compact, so Mathlib's descent instance
for local finite type along surjective flat quasi-compact morphisms applies. This
instance already supplies the faithfully-flat finite-generation argument of 02KX. -/
theorem locallyOfFiniteType_of_fpqcCover
    {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v} (S' : I → Scheme.{u})
    (g : ∀ i, S' i ⟶ S) (hcover : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, LocallyOfFiniteType (pullback.snd f (g i))) :
    LocallyOfFiniteType f := by
  refine fpqc_local_on_base_criterion @LocallyOfFiniteType ?_ ?_ f g hcover h
  · intro X S T f g _ hf
    have : LocallyOfFiniteType f := hf
    infer_instance
  · intro S T X _ _ f g hflat hsurj hft
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @LocallyOfFiniteType)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ hft

end AlgebraicGeometry
