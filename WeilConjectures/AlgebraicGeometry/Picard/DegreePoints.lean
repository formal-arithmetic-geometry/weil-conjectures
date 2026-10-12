/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian

/-!
# The rational points of `Pic^d`

Let `X` be a smooth projective geometrically integral curve over a separably closed field `k`.
For every `d ∈ ℤ`, the `k`-points of the degree-`d` part `Pic^d_{X/k}` of the relative Picard
functor are the invertible modules of degree `d` on `X`. For `d = 0` this is
`AlgebraicGeometry.exists_picardZero_equiv_picardFunctorDegree_zero`.

## Main statements

- `AlgebraicGeometry.exists_picardDegree_equiv_picardFunctorDegree`: the bijection between the
  classes of degree `d` in `Pic X` and `Pic^d_{X/k}(k)` (blueprint
  `thm-sc-theorem-of-the-base`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **The `k`-points of `Pic^d_{X/k}` are the invertible modules of degree `d`.** For a smooth
projective geometrically integral curve `X` over a separably closed field `k` and `d ∈ ℤ`, the
map sending a class `ℒ ∈ Pic X` of degree `d` to the image of its pullback to `X ×_k k` is a
bijection onto `Pic^d_{X/k}(k)`. By the split exact sequence with `T = Spec k` and
`Pic (Spec k) = 0`, `Pic_{X/k}(k) = Pic X`, and the sections of `Pic^d_{X/k}` are the sections of
`Pic_{X/k}` of degree `d` (`AlgebraicGeometry.exists_picardFunctorDegreeι_app_eq`).

(blueprint: `thm-sc-theorem-of-the-base`, the `k`-points of `Pic^d_{C/k}`) -/
theorem exists_picardDegree_equiv_picardFunctorDegree [IsSepClosed k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] (d : ℤ) :
    ∃ Φ : {L : X.Pic // picDegreeHom k X L = .ofAdd d} ≃
      (picardFunctorDegree (X ↘ Spec (.of k)) d).obj.obj (.op (𝟙_ (Over (Spec (.of k))))),
      ∀ L, ∃ h, Φ L = (toSheafify (fppfTopology.over (Spec (.of k)))
        (picardSubfunctorDegree (X ↘ Spec (.of k)) d).toFunctor).app _
          ⟨Pic.map (pullback.fst (X ↘ Spec (.of k)) (𝟙_ (Over (Spec (.of k)))).hom) L.1, h⟩ := by
  set f := X ↘ Spec (.of k)
  let T₀ := 𝟙_ (Over (Spec (.of k)))
  let J := fppfTopology.over (Spec (.of k))
  let S := picardSubfunctorDegree f d
  -- a class of degree `d` on `X` pulls back to a class of fibrewise degree `d` on `X_k`
  have hmem (L : {L : X.Pic // picDegreeHom k X L = .ofAdd d}) :
      Pic.map (pullback.fst f T₀.hom) L.1 ∈ S.obj (.op T₀) := by
    intro K _ _ t
    rw [picardFibreDegree_map_fst]
    have h := L.2
    rw [picDegreeHom_apply, Hom.picDegree_eq] at h
    exact Multiplicative.ofAdd.injective h
  -- the split exact sequence at `T₀ = Spec k`
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨pt⟩ := Hom.nonempty_fieldPoints (k := k) f
  have hσ : pt.1 ≫ f = 𝟙 _ := by
    rw [pt.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hsplit := bijective_pic_split f pt.1 hσ
    isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral T₀
  have hone (a : (Spec (.of k)).Pic) : a = 1 := by
    obtain ⟨e⟩ := Modules.IsInvertible.nonempty_iso_unit (X := Spec (.of k)) default
      ((fromSkeleton _).obj a.val)
    exact Pic.eq_iff_nonempty_iso.2 ⟨e ≪≫ Pic.oneIso.symm⟩
  -- `X_k ⟶ X` is an isomorphism
  have : IsIso (pullback.fst f T₀.hom) := inferInstanceAs (IsIso (pullback.fst f (𝟙 _)))
  have hinv (L : X.Pic) :
      Pic.map (inv (pullback.fst f T₀.hom)) (Pic.map (pullback.fst f T₀.hom) L) = L := by
    rw [← Pic.map_comp, IsIso.inv_hom_id, Pic.map_id]
  have hinv' (M : (pullback f T₀.hom).Pic) :
      Pic.map (pullback.fst f T₀.hom) (Pic.map (inv (pullback.fst f T₀.hom)) M) = M := by
    rw [← Pic.map_comp, IsIso.hom_inv_id, Pic.map_id]
  let φ (L : {L : X.Pic // picDegreeHom k X L = .ofAdd d}) :
      (picardFunctorDegree f d).obj.obj (.op T₀) :=
    (toSheafify J S.toFunctor).app _ ⟨_, hmem L⟩
  refine ⟨Equiv.ofBijective φ ⟨fun L₁ L₂ h ↦ ?_, fun s ↦ ?_⟩, fun L ↦ ⟨hmem L, rfl⟩⟩
  · have h' := congrArg ((picardFunctorDegreeι f d).hom.app _) h
    simp only [φ] at h'
    rw [picardFunctorDegreeι_app_toSheafify, picardFunctorDegreeι_app_toSheafify] at h'
    have hM := hsplit.1 (a₁ := Pic.map (pullback.fst f T₀.hom) L₁.1)
      (a₂ := Pic.map (pullback.fst f T₀.hom) L₂.1) (Prod.ext ((hone _).trans (hone _).symm) h')
    exact Subtype.ext (by rw [← hinv L₁.1, hM, hinv])
  · -- the image of `s` in `Pic_{X/k}(k)` comes from a class `M` on `X_k` of degree `d`
    obtain ⟨M, hM⟩ := hsplit.2 (1, (picardFunctorDegreeι f d).hom.app _ s)
    have hM₂ : (toPicardFunctor f).app _ M = (picardFunctorDegreeι f d).hom.app _ s :=
      congrArg Prod.snd hM
    have hMS : M ∈ S.obj (.op T₀) := (mem_picardSubfunctorDegree_iff f d M).2 fun t ↦ by
      rw [← picardDegree_toPicardFunctor, hM₂]
      exact picardDegree_picardFunctorDegreeι f d s t
    have hL₀ : picDegreeHom k X (Pic.map (inv (pullback.fst f T₀.hom)) M) = .ofAdd d := by
      have h := hMS k (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k k)))
        (Category.comp_id _))
      rw [← hinv' M, picardFibreDegree_map_fst] at h
      rw [picDegreeHom_apply, Hom.picDegree_eq, h]
    refine ⟨⟨_, hL₀⟩, injective_picardFunctorDegreeι_app f d T₀ ?_⟩
    simp only [φ]
    rw [picardFunctorDegreeι_app_toSheafify]
    dsimp only
    rw [hinv' M]
    exact hM₂

end AlgebraicGeometry
