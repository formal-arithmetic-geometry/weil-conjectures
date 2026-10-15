/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Trivial Kan fibrations between coskeletal simplicial sets

Source: Stacks Project, Simplicial Methods, Lemma 14.32.1, Tag 01A6
(blueprint: lem-weil-pbc-coskeletal-map-trivial-kan).
-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

private lemma simplex_postcomp_injective {V U : SSet.{u}} (f : V ⟶ U) (i : ℕ)
    (hi : Function.Injective (f.app (Opposite.op (SimplexCategory.mk i)))) :
    Function.Injective (fun a : stdSimplex.obj (SimplexCategory.mk i) ⟶ V ↦ a ≫ f) := by
  intro a b hab
  apply yonedaEquiv.injective
  apply hi
  simpa only [← yonedaEquiv_comp] using congrArg yonedaEquiv hab

private lemma boundary_lift_low {V U : SSet.{u}} (f : V ⟶ U) (m : ℕ)
    (hs : Function.Surjective (f.app (Opposite.op (SimplexCategory.mk m))))
    (hi : ∀ i : ℕ, i < m → Function.Injective (f.app (Opposite.op (SimplexCategory.mk i)))) :
    HasLiftingProperty (boundary.{u} m).ι f := by
  constructor
  intro a b sq
  obtain ⟨y, hy⟩ := hs (yonedaEquiv b)
  let c : stdSimplex.obj (SimplexCategory.mk m) ⟶ V := yonedaEquiv.symm y
  have hc : c ≫ f = b := by
    apply yonedaEquiv.injective
    simpa only [c, yonedaEquiv_comp, Equiv.apply_symm_apply] using hy
  apply CommSq.HasLift.mk'
  refine { l := c, fac_right := hc, fac_left := ?_ }
  cases m with
  | zero => exact boundary.hom_ext₀
  | succ m =>
    apply boundary.hom_ext
    intro i
    apply simplex_postcomp_injective f m (hi m (by omega))
    simp only [Category.assoc, hc, boundary.ι_ι_assoc, sq.w]

private lemma truncation_map_bijective (W : SSet.{u}) (n : ℕ)
    (hW : IsIso ((coskAdj n).unit.app W)) (K : SSet.{u}) :
    Function.Bijective (fun g : K ⟶ W ↦ (truncation n).map g) := by
  let e : (K ⟶ W) ≃ ((truncation n).obj K ⟶ (truncation n).obj W) :=
    (Iso.homCongr (Iso.refl K) (asIso ((coskAdj n).unit.app W))).trans
      ((coskAdj n).homEquiv K ((truncation n).obj W)).symm
  have he (g : K ⟶ W) : e g = (truncation n).map g := by
    dsimp [e]
    rw [Adjunction.homEquiv_symm_apply]
    change (truncation n).map (g ≫ (coskAdj n).unit.app W) ≫
      (coskAdj n).counit.app ((truncation n).obj W) = _
    rw [Functor.map_comp, Category.assoc]
    simp
  simpa only [show (fun g ↦ (truncation n).map g) = e from funext (fun g ↦ (he g).symm)]
    using e.bijective

private lemma boundary_lift_high {V U : SSet.{u}} (f : V ⟶ U) (n m : ℕ)
    (hm : n < m)
    (hU : IsIso ((coskAdj n).unit.app U))
    (hV : IsIso ((coskAdj n).unit.app V)) :
    HasLiftingProperty (boundary.{u} m).ι f := by
  let j := (boundary.{u} m).ι
  have hj : IsIso ((truncation n).map j) := by
    have (i : (SimplexCategory.Truncated n)ᵒᵖ) :
        IsIso (((truncation n).map j).app i) := by
      apply (isIso_iff_bijective _).2
      change Function.Bijective
        (fun x : (boundary.{u} m).toSSet.obj (Opposite.op i.unop.obj) ↦ x.val)
      refine ⟨Subtype.val_injective, ?_⟩
      intro x
      refine ⟨⟨x, ?_⟩, rfl⟩
      have h : (boundary.{u} m).obj (Opposite.op i.unop.obj) = Set.univ :=
        boundary_obj_eq_univ i.unop.obj.len m (lt_of_le_of_lt i.unop.property hm)
      rw [h]
      trivial
    exact NatIso.isIso_of_isIso_app _
  have hr (W : SSet.{u}) (hW : IsIso ((coskAdj n).unit.app W)) :
      Function.Bijective
        (fun g : stdSimplex.obj (SimplexCategory.mk m) ⟶ W ↦ j ≫ g) := by
    have hK := truncation_map_bijective W n hW (stdSimplex.obj (SimplexCategory.mk m))
    have hB := truncation_map_bijective W n hW (boundary m).toSSet
    constructor
    · intro a b hab
      apply hK.1
      apply (cancel_epi ((truncation n).map j)).1
      simpa only [← Functor.map_comp] using congrArg ((truncation n).map) hab
    · intro a
      obtain ⟨b, hb⟩ := hK.2 (inv ((truncation n).map j) ≫ (truncation n).map a)
      refine ⟨b, hB.1 ?_⟩
      dsimp only at hb ⊢
      rw [Functor.map_comp, hb]
      simp
  constructor
  intro a b sq
  obtain ⟨c, hc⟩ := (hr V hV).2 a
  apply CommSq.HasLift.mk'
  refine { l := c, fac_left := hc, fac_right := ?_ }
  apply (hr U hU).1
  simpa only [← Category.assoc, hc] using sq.w

/-- Stacks Project, Simplicial Methods, Lemma 14.32.1 (Tag 01A6)
(blueprint: lem-weil-pbc-coskeletal-map-trivial-kan).
A map between `n`-coskeletal simplicial sets which is bijective below `n` and surjective
in degree `n` is a trivial Kan fibration.

Proof: use the boundary lifting characterization of
[def-weil-pbc-trivial-kan-fibration]. First, the map in degree zero is surjective: use the
surjectivity assumption if `n = 0`, and bijectivity below `n` otherwise.
For a boundary lifting problem in degree `1 ≤ k ≤ n`, choose a preimage of the simplex
in the target. Yoneda gives the corresponding map from the standard simplex
[def-weil-pbc-simplicial-set]. It agrees with the given boundary map: every nonsurjective
simplex factors through a face [lem-weil-pbc-simplex-face-factorization], and the two
face values have equal images under the injective map in degree `k - 1 < n`.
For either of the coskeletal objects `W = U, V`, the coskeleton adjunction and the
invertible unit give a bijection between maps `K → W` and maps between their
`n`-truncations [def-weil-pbc-simplicial-coskeleton]. When `k > n`, the boundary inclusion
is an isomorphism in all degrees at most `n`: a map `[j] → [k]` with `j ≤ n < k` cannot
be surjective. Thus restriction from the standard simplex to its boundary induces a
bijection on maps into either `U` or `V`. Extend the given boundary map uniquely into
`V`; its composite with `f` equals the given simplex into `U`, because their restrictions
agree and restriction into `U` is injective. These lifts, including degree zero, give the
right lifting property against every boundary inclusion. -/
theorem rlp_boundaries_of_coskeletal_map {V U : SSet.{u}} (f : V ⟶ U) (n : ℕ)
    (hbij : ∀ i : ℕ, i < n → Function.Bijective (f.app (Opposite.op (SimplexCategory.mk i))))
    (hsurj : Function.Surjective (f.app (Opposite.op (SimplexCategory.mk n))))
    (hU : IsIso ((coskAdj n).unit.app U))
    (hV : IsIso ((coskAdj n).unit.app V)) :
    modelCategoryQuillen.I.rlp f := by
  intro X Y g hg
  change MorphismProperty.ofHoms (fun n ↦ (boundary.{u} n).ι) g at hg
  rcases hg with ⟨m⟩
  by_cases hm : m ≤ n
  · apply boundary_lift_low f m
    · obtain h | rfl := hm.lt_or_eq
      · exact (hbij m h).2
      · exact hsurj
    · intro i hi
      exact (hbij i (lt_of_lt_of_le hi hm)).1
  · exact boundary_lift_high f n m (Nat.lt_of_not_ge hm) hU hV

end SSet
