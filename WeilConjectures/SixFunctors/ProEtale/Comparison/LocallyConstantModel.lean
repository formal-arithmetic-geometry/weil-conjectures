/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.TrivializationSections
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LocallyConstantOrigin
public import WeilConjectures.ConstructibleSheaf.FiniteEtalePushforward
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf

/-!
# Étale sheaves whose comparison pullback is locally constant

Let `Λ` be a finite ring and `G` a sheaf of `Λ`-modules on the small étale site of a scheme `Y`
such that the comparison pullback `ν^* G` is, on the members of a pro-étale covering family, the
constant sheaf of a finite `Λ`-module. Then `G` is finite locally constant
(`AlgebraicGeometry.ProEtale.isFiniteLocallyConstantSheaf_of_comparisonUpperStar`).

Let `y` be a point of `Y`. The proof runs as follows.

1. There is a weakly étale affine `V = lim Uⱼ ⟶ Y`, a cofiltered limit of affine étale
   `Y`-schemes, through whose image passes `y` and over which `ν^* G` is constant with value a
   finite module `M` (`AlgebraicGeometry.ProEtale.exists_affineProEt_comp_eq`, the density of
   the affine pro-étale site).
2. The sections of `ν^* G` over `V` are the colimit of the sections over the `Uⱼ`
   (`AlgebraicGeometry.ProEtale.isColimit_comparisonUpperStar_mapCocone`); the trivialization
   over `V`, a linear map `M ⟶ Γ(V, ν^* G)`, factors through `Γ(U, ν^* G)` for some
   `U = Uⱼ` (`AlgebraicGeometry.ProEtale.exists_linearMap_lift_of_isColimit`).
3. Over every member `W ⟶ Y` of the trivializing covering family, the sections of `ν^* G`
   are locally constant functions to a finite module, so the image of `M` gives at every
   point of `W ×_Y U` a linear map, which is bijective on an open subset, independent of
   the member of the family by the transition maps
   (`AlgebraicGeometry.ProEtale.bijective_trivTransition`), and whose image in `U` is open,
   the members of a pro-étale covering family being jointly a quotient map. It contains the
   image of `V`.
4. On that open subscheme `O ⊆ U` the map `M_O ⟶ ν^* G|_O` is locally bijective, hence an
   isomorphism, so that `G|_O ≅ M_O` by full faithfulness of `ν^*`.
-/

@[expose] public section

universe v w u

open CategoryTheory Limits Opposite

/-- **Linear maps from a finite module to a filtered colimit factor through a stage**, for a
finite coefficient ring: the finitely many values lift to a common stage, and the finitely many
linear relations among them hold at a later stage. -/
lemma CategoryTheory.Limits.exists_linearMap_lift_of_isColimit {Λ : Type v} [CommRing Λ]
    [Finite Λ] {J : Type w} [Category J] [IsFiltered J] {K : J ⥤ ModuleCat.{v} Λ}
    {c : Cocone K} (hc : IsColimit c) [PreservesColimit K (forget (ModuleCat.{v} Λ))]
    (M : Type*) [AddCommGroup M] [Module Λ M] [Finite M] (b : M →ₗ[Λ] c.pt) :
    ∃ (j : J) (a : M →ₗ[Λ] K.obj j), ∀ m, c.ι.app j (a m) = b m := by
  classical
  have := Fintype.ofFinite M
  have := Fintype.ofFinite Λ
  -- lift the values to a common stage
  choose jm ym hym using fun m : M ↦ Concrete.isColimit_exists_rep K hc (b m)
  let O₁ : Finset J := Finset.univ.image jm
  have hO₁ (m : M) : jm m ∈ O₁ := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  let k₀ := IsFiltered.sup O₁ ∅
  let a₀ (m : M) : K.obj k₀ := K.map (IsFiltered.toSup O₁ ∅ (hO₁ m)) (ym m)
  have ha₀ (m : M) : c.ι.app k₀ (a₀ m) = b m := by
    rw [← hym m, ← c.w (IsFiltered.toSup O₁ ∅ (hO₁ m))]
    rfl
  -- the linear relations hold at later stages
  let E := (M × M) ⊕ (Λ × M)
  let x : E → K.obj k₀
    | .inl (m, m') => a₀ (m + m') - a₀ m - a₀ m'
    | .inr (r, m) => a₀ (r • m) - r • a₀ m
  have hx (e : E) : c.ι.app k₀ (x e) = c.ι.app k₀ 0 := by
    rcases e with ⟨m, m'⟩ | ⟨r, m⟩
    · simp only [x, map_sub, ha₀, map_add, map_zero]
      first | abel | (abel_nf; exact sub_self _) | simp
    · simp only [x, map_sub, ha₀, map_smul, map_zero, sub_self]
  choose ke fe ge hfe using fun e ↦ Concrete.isColimit_exists_of_rep_eq K hc _ _ (hx e)
  let O₂ : Finset J := insert k₀ (Finset.univ.image ke)
  have hk₀ : k₀ ∈ O₂ := Finset.mem_insert_self _ _
  have hke (e : E) : ke e ∈ O₂ :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  let H : Finset (Σ' (X Y : J) (_ : X ∈ O₂) (_ : Y ∈ O₂), X ⟶ Y) :=
    Finset.univ.image fun e ↦ ⟨k₀, ke e, hk₀, hke e, fe e⟩
  obtain ⟨S, T, hT⟩ := IsFiltered.sup_exists O₂ H
  have hzero (e : E) : K.map (T hk₀) (x e) = 0 := by
    rw [← hT hk₀ (hke e) (Finset.mem_image_of_mem _ (Finset.mem_univ e)), K.map_comp,
      ConcreteCategory.comp_apply, hfe e, map_zero, map_zero]
  refine ⟨S, { toFun m := K.map (T hk₀) (a₀ m), map_add' m m' := ?_, map_smul' r m := ?_ },
    fun m ↦ ?_⟩
  · have := hzero (.inl (m, m'))
    simp only [x, map_sub] at this
    rw [sub_sub, sub_eq_zero] at this
    simp only [this]
  · have := hzero (.inr (r, m))
    simp only [x, map_sub, map_smul] at this
    rw [sub_eq_zero] at this
    simp only [this, RingHom.id_apply]
  · change c.ι.app S (K.map (T hk₀) (a₀ m)) = b m
    rw [← ConcreteCategory.comp_apply, c.w]
    exact ha₀ m

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **Density of the affine pro-étale site.** Every point of a weakly étale `Y`-scheme `W` lies
in the image of a `Y`-morphism from an object of the affine pro-étale site of `Y`. -/
lemma exists_affineProEt_comp_eq {Y W : Scheme.{u}} (g : W ⟶ Y) [WeaklyEtale g] (w : W) :
    ∃ (V : Y.AffineProEt) (v : V.left ⟶ W) (_ : v ≫ g = V.hom), w ∈ Set.range v := by
  obtain ⟨R, hR, hRS⟩ := (ProEt.mem_topology_iff (V := Scheme.ProEt.mk g)).1
    ((AffineProEt.toProEt Y).is_cover_of_isCoverDense (ProEt.topology Y) (Scheme.ProEt.mk g))
  have hR' := (ProEt.mem_precoverage_iff.1 hR).2.1
  obtain ⟨Z, f', hf, t, ht⟩ :=
    (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).1 hR' w
  obtain ⟨T, f, hf⟩ := hf
  obtain ⟨⟨V, l, m, hlm⟩⟩ := hRS _ hf
  subst ht
  refine ⟨V, m.left, by simpa using MorphismProperty.Over.w m, l.left t, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← MorphismProperty.Comma.comp_left, hlm]
  rfl

end AlgebraicGeometry.ProEtale
