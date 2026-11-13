/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier


/-!
# The finite-field Artin–Schreier map

The finite-field specialization of the affine-line Artin–Schreier map is finite étale,
surjective, translation-invariant, and trivialized by the translations indexed by the field.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AffineSpace

/-- For a finite field `k`, the map `t ↦ t ^ |k| - t` on the affine line is finite étale and
  surjective, invariant under translations by `k`, and its canonical translation torsor map is an
  isomorphism. -/
theorem finiteField_artinSchreier_map (k : Type u) [Field k] [Fintype k] :
    IsFinite (artinSchreierMap PUnit.{u + 1} (Spec (.of k)) (Fintype.card k)) ∧
      Etale (artinSchreierMap PUnit.{u + 1} (Spec (.of k)) (Fintype.card k)) ∧
      Function.Surjective
        (artinSchreierMap PUnit.{u + 1} (Spec (.of k)) (Fintype.card k)).base ∧
      (∀ c : k,
        translation (fun _ : PUnit.{u + 1} ↦ (Scheme.ΓSpecIso (.of k)).inv.hom c) ≫
            artinSchreierMap PUnit.{u + 1} (Spec (.of k)) (Fintype.card k) =
          artinSchreierMap PUnit.{u + 1} (Spec (.of k)) (Fintype.card k)) ∧
      IsIso (artinSchreierTorsorMap (n := PUnit.{u + 1}) (S := Spec (.of k)) k
        (Scheme.ΓSpecIso (.of k)).inv.hom) := by
  refine ⟨isFinite_artinSchreierMap _ _ Fintype.one_lt_card.ne', ?_,
    surjective_artinSchreierMap k, ?_, ?_⟩
  · apply etale_artinSchreierMap
    rw [← map_natCast (Scheme.ΓSpecIso (.of k)).inv.hom,
      FiniteField.cast_card_eq_zero, map_zero]
  · intro c
    exact translation_comp_artinSchreierMap_of_finiteField k
      (Scheme.ΓSpecIso (.of k)).inv.hom (fun _ ↦ c)
  · exact isIso_artinSchreierTorsorMap (S := Spec (.of k)) k
      (Scheme.ΓSpecIso (.of k)).inv.hom

end AlgebraicGeometry.AffineSpace

end
