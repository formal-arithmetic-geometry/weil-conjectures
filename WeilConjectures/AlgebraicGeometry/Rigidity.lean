/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The rigidity theorem

A morphism out of a product `X × Y` whose second factor `Y` is proper cannot collapse one fibre
`{x₀} × Y` to a point without being independent of the second variable altogether. This file
proves that statement, `AlgebraicGeometry.existsUnique_comp_fst_eq_of_isProper`, together with
the two lemmas its proof rests on.

Products are formed as `Limits.pullback πX πY` of the two structure morphisms rather than as
`X ⊗ Y` in `Over (Spec (.of K))`: the Mathlib lemmas used below (stability of `IsProper`,
`Surjective` and `GeometricallyIntegral` under base change, and
`AlgebraicGeometry.ext_of_apply_eq`) are all stated for bare schemes, so the bare pullback needs
no translation.

Following the project convention there is no `IsVariety` predicate: "variety over `K`" is spelled
out as the typeclass assumptions actually used on the structure morphism, namely
`[LocallyOfFiniteType π]` and `[GeometricallyIntegral π]` with `K` algebraically closed.

Beware that Lean's composition `f ≫ g` is the classical `g ∘ f`, the opposite order to the
blueprint.

## Main statements

- `AlgebraicGeometry.existsUnique_comp_eq_of_isProper_of_isAffine`
  (blueprint `lem:cube-constant-to-affine`): a morphism from a proper integral `K`-scheme `Y` to
  an affine `K`-scheme `V` factors uniquely through the structure morphism `Y ⟶ Spec K`, by a
  `K`-rational point of `V`. In particular its set-theoretic image is a single point.
- `AlgebraicGeometry.exists_isOpen_image_preimage_subset`
  (blueprint `lem:cube-collapse-neighbourhood`): if `f : X ×[K] Y ⟶ Z` maps the fibre
  `{x₀} × Y` into an open set `U` and `Y` is proper over `K`, then already `f` maps
  `p_X ⁻¹' V` into `U` for some open neighbourhood `V` of `x₀`.
- `AlgebraicGeometry.existsUnique_comp_fst_eq_of_isProper`
  (blueprint `thm:cube-rigidity`): **rigidity**. For `X` a variety over an algebraically closed
  field `K`, `Y` a proper variety over `K` and `Z` separated and locally of finite type over
  `K`, a morphism `f : X ×[K] Y ⟶ Z` collapsing one fibre `{x₀} × Y` to a point factors as
  `f = p_X ≫ h` for a unique `h : X ⟶ Z`.
- `AlgebraicGeometry.comp_fst_lift_comp_eq_of_isProper`: the `h` of the previous item is
  `σ ≫ f` for the section `σ = (id, y₀)` of `p_X` attached to any `K`-rational point `y₀`
  of `Y`, which is the "namely" clause of `thm:cube-rigidity`.

The properness hypothesis is on `Y`, the factor that collapses, and cannot be moved to `X`: with
`X = Z = ℙ¹`, `Y = 𝔸¹` and `f ([u : v], t) = [u : v + t * u]` the fibre over `[0 : 1]` collapses
while `f` does depend on `t`.

## References

* [Mumford, *Abelian varieties*][MumfordAbelianVarieties], §4
* [Milne, *Abelian varieties*][MilneAbelianVarieties], I §1

-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K]

section ConstantToAffine

variable {Y V : Scheme.{u}}

/-- **A morphism from a proper integral variety to an affine scheme is constant.**

If `Y` is a proper integral scheme over an algebraically closed field `K` and `g : Y ⟶ V` is a
morphism of `K`-schemes with `V` affine, then `g` factors as `π ≫ v` for a unique `K`-rational
point `v : Spec K ⟶ V`. In particular the set-theoretic image of `g` is the single point `v`.

This is `lem:cube-constant-to-affine` of the blueprint. -/
theorem existsUnique_comp_eq_of_isProper_of_isAffine [IsAlgClosed K] (π : Y ⟶ Spec (.of K))
    [IsIntegral Y] [IsProper π] (q : V ⟶ Spec (.of K)) [IsAffine V] (g : Y ⟶ V)
    (hg : g ≫ q = π) :
    ∃! v : Spec (.of K) ⟶ V, v ≫ q = 𝟙 _ ∧ π ≫ v = g := by
  obtain ⟨s, hs⟩ := exists_comp_eq_id π
  have hiso : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop) :=
    isIso_ΓSpecIso_inv_comp_appTop π
  have hiso' : IsIso (Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop)) := inferInstance
  have h1 : Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop) = π := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have h2 : Y.toSpecΓ = π ≫ inv (Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop)) := by
    rw [IsIso.eq_comp_inv]
    exact h1
  have h3 : Y.toSpecΓ ≫ Spec.map g.appTop ≫ V.isoSpec.inv = g := by
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have h4 : s ≫ Y.toSpecΓ = inv (Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop)) := by
    rw [h2, ← Category.assoc, hs, Category.id_comp]
  refine ⟨s ≫ g, ⟨by rw [Category.assoc, hg, hs], ?_⟩, ?_⟩
  · calc π ≫ s ≫ g
        = π ≫ (s ≫ Y.toSpecΓ) ≫ Spec.map g.appTop ≫ V.isoSpec.inv := by
          rw [Category.assoc, h3]
      _ = Y.toSpecΓ ≫ Spec.map g.appTop ≫ V.isoSpec.inv := by rw [h4, ← Category.assoc, ← h2]
      _ = g := h3
  · rintro v ⟨-, hv⟩
    rw [← hv, ← Category.assoc, hs, Category.id_comp]

end ConstantToAffine

section CollapseNeighbourhood

variable {X Y Z : Scheme.{u}}

/-- **Properness makes the collapsing locus open.**

Let `X` and `Z` be `K`-schemes and let `Y` be proper over `K`. If a morphism
`f : X ×[K] Y ⟶ Z` maps the fibre `p_X ⁻¹' {x₀}` into an open set `U`, then there is an open
neighbourhood `V` of `x₀` with `f '' (p_X ⁻¹' V) ⊆ U`.

This is `lem:cube-collapse-neighbourhood` of the blueprint. -/
theorem exists_isOpen_image_preimage_subset (πX : X ⟶ Spec (.of K)) (πY : Y ⟶ Spec (.of K))
    [IsProper πY] (f : pullback πX πY ⟶ Z) (x₀ : X) (U : Set Z) (hU : IsOpen U)
    (hfx₀ : ⇑f '' (⇑(pullback.fst πX πY) ⁻¹' {x₀}) ⊆ U) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ ⇑f '' (⇑(pullback.fst πX πY) ⁻¹' V) ⊆ U := by
  -- `p_X` is the base change of the proper morphism `πY`, hence a closed map.
  have hclosed : IsClosedMap ⇑(pullback.fst πX πY) := (pullback.fst πX πY).isClosedMap
  -- `W := f ⁻¹' Uᶜ` is closed, so `p_X '' W` is closed; take `V` to be its complement.
  set W : Set ↥(pullback πX πY) := ⇑f ⁻¹' Uᶜ
  have hWclosed : IsClosed W := hU.isClosed_compl.preimage f.continuous
  refine ⟨(⇑(pullback.fst πX πY) '' W)ᶜ, (hclosed W hWclosed).isOpen_compl, ?_, ?_⟩
  · rintro ⟨w, hw, hwx⟩
    exact hw (hfx₀ ⟨w, hwx, rfl⟩)
  · rintro _ ⟨w, hw, rfl⟩
    by_contra hfw
    exact hw ⟨w, hfw, rfl⟩

end CollapseNeighbourhood

section Rigidity

variable {X Y Z : Scheme.{u}}

/-- **The rigidity theorem.**

Let `K` be an algebraically closed field, let `X` be a variety over `K`, let `Y` be a proper
variety over `K` and let `Z` be separated and locally of finite type over `K`. If a morphism of
`K`-schemes `f : X ×[K] Y ⟶ Z` collapses the fibre `{x₀} × Y` to a single point `z₀`, then there
is a unique `h : X ⟶ Z` with `f = p_X ≫ h`; in other words `f` does not depend on the second
variable.

Note that properness is hypothesised on `Y`, the factor that collapses, and cannot be moved
to `X`.

This is `thm:cube-rigidity` of the blueprint. -/
theorem existsUnique_comp_fst_eq_of_isProper [IsAlgClosed K] (πX : X ⟶ Spec (.of K))
    (πY : Y ⟶ Spec (.of K)) (πZ : Z ⟶ Spec (.of K))
    [LocallyOfFiniteType πX] [GeometricallyIntegral πX]
    [IsProper πY] [GeometricallyIntegral πY]
    [IsSeparated πZ] [LocallyOfFiniteType πZ]
    (f : pullback πX πY ⟶ Z) (hf : f ≫ πZ = pullback.fst πX πY ≫ πX)
    (x₀ : X) (z₀ : Z) (hx₀ : ⇑f '' (⇑(pullback.fst πX πY) ⁻¹' {x₀}) = {z₀}) :
    ∃! h : X ⟶ Z, pullback.fst πX πY ≫ h = f := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton πX
  have : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton πY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian πY
  have hint : IsIntegral (pullback πX πY) := inferInstance
  -- a `K`-rational point `y₀` of `Y`, and the resulting section `σ` of `p_X`
  obtain ⟨y₀, hy₀⟩ := exists_comp_eq_id πY
  obtain ⟨σ, hσfst, hσsnd⟩ : ∃ σ : X ⟶ pullback πX πY,
      σ ≫ pullback.fst πX πY = 𝟙 X ∧ σ ≫ pullback.snd πX πY = πX ≫ y₀ :=
    ⟨pullback.lift (𝟙 X) (πX ≫ y₀) (by simp [hy₀]), by simp, by simp⟩
  refine ⟨σ ≫ f, ?_, ?_⟩
  swap
  · rintro h rfl
    rw [← Category.assoc, hσfst, Category.id_comp]
  -- `h ≫ πZ = πX`, so `f` and `p_X ≫ h` are both morphisms of `K`-schemes.
  have hhZ : (σ ≫ f) ≫ πZ = πX := by
    rw [Category.assoc, hf, ← Category.assoc, hσfst, Category.id_comp]
  have hfZ : LocallyOfFiniteType (f ≫ πZ) := by rw [hf]; infer_instance
  have hfZ' : LocallyOfFiniteType ((pullback.fst πX πY ≫ σ ≫ f) ≫ πZ) := by
    rw [Category.assoc, hhZ]; infer_instance
  -- Step 1: an affine open `U` around `z₀` and an open `V ∋ x₀` with `f '' (p_X ⁻¹' V) ⊆ U`.
  obtain ⟨U, hU, hz₀U⟩ : ∃ U : Z.Opens, IsAffineOpen U ∧ z₀ ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hz₀U, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z₀) isOpen_univ
    exact ⟨U, hU, hz₀U⟩
  have : IsAffine U.toScheme := hU
  obtain ⟨V, hVopen, hx₀V, hVU⟩ := exists_isOpen_image_preimage_subset πX πY f x₀ (U : Set Z)
    U.isOpen (by rw [hx₀]; simpa using hz₀U)
  -- Step 3: it suffices to check the equality at the closed points of the dense open `p_X ⁻¹' V`.
  refine ext_of_apply_eq πZ (⇑(pullback.fst πX πY) ⁻¹' V)
    (hVopen.preimage (pullback.fst πX πY).continuous).isLocallyClosed
    ((hVopen.preimage (pullback.fst πX πY).continuous).dense ?_) ?_ ?_
  · obtain ⟨c, hc⟩ := (pullback.fst πX πY).surjective x₀
    exact ⟨c, by simpa [hc] using hx₀V⟩
  -- Step 2: `f` and `p_X ≫ (σ ≫ f)` agree at the `K`-rational points of `p_X ⁻¹' V`.
  · intro c hcV hc
    obtain ⟨c', hc'comp, hc'apply⟩ : ∃ c' : Spec (.of K) ⟶ pullback πX πY,
        c' ≫ pullback.fst πX πY ≫ πX = 𝟙 _ ∧ c' (IsLocalRing.closedPoint K) = c :=
      ⟨pointOfClosedPoint (pullback.fst πX πY ≫ πX) c hc, pointOfClosedPoint_comp _ _ _,
        pointOfClosedPoint_apply _ _ _ _⟩
    obtain ⟨x, hxdef⟩ : ∃ x : Spec (.of K) ⟶ X, x = c' ≫ pullback.fst πX πY := ⟨_, rfl⟩
    obtain ⟨y, hydef⟩ : ∃ y : Spec (.of K) ⟶ Y, y = c' ≫ pullback.snd πX πY := ⟨_, rfl⟩
    have hxπ : x ≫ πX = 𝟙 _ := by rw [hxdef, Category.assoc, hc'comp]
    have hyπ : y ≫ πY = 𝟙 _ := by
      rw [hydef, Category.assoc, ← pullback.condition]; exact hc'comp
    -- the fibre `{x} × Y`, as a morphism `Y ⟶ X ×[K] Y`
    obtain ⟨i, hifst, hisnd⟩ : ∃ i : Y ⟶ pullback πX πY,
        i ≫ pullback.fst πX πY = πY ≫ x ∧ i ≫ pullback.snd πX πY = 𝟙 Y :=
      ⟨pullback.lift (πY ≫ x) (𝟙 Y) (by simp [hxπ]), by simp, by simp⟩
    have hc'i : c' = y ≫ i := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hifst, ← Category.assoc, hyπ, Category.id_comp, hxdef]
      · rw [Category.assoc, hisnd, Category.comp_id, hydef]
    have hσi : x ≫ σ = y₀ ≫ i := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hσfst, Category.comp_id, Category.assoc, hifst, ← Category.assoc,
          hy₀, Category.id_comp]
      · rw [Category.assoc, hσsnd, Category.assoc, hisnd, Category.comp_id, ← Category.assoc,
          hxπ, Category.id_comp]
    -- the image of `{x} × Y` lies in the affine open `U`
    have hxpt : ∀ a : (Spec (.of K) : Scheme), x a = pullback.fst πX πY c := by
      intro a
      rw [Subsingleton.elim a (IsLocalRing.closedPoint K), hxdef, Scheme.Hom.comp_apply, hc'apply]
    have hrange : Set.range ⇑(i ≫ f) ⊆ Set.range ⇑U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      refine hVU ⟨i w, ?_, ?_⟩
      · have h : pullback.fst πX πY (i w) = x (πY w) := by
          rw [← Scheme.Hom.comp_apply, hifst, Scheme.Hom.comp_apply]
        change pullback.fst πX πY (i w) ∈ V
        rw [h, hxpt]
        exact hcV
      · rw [Scheme.Hom.comp_apply]
    -- the fibre maps to the affine `U`, hence is constant there
    obtain ⟨v, ⟨-, hv⟩, -⟩ := existsUnique_comp_eq_of_isProper_of_isAffine πY (U.ι ≫ πZ)
      (IsOpenImmersion.lift U.ι (i ≫ f) hrange) (by
        rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hf, ← Category.assoc,
          hifst, Category.assoc, hxπ, Category.comp_id])
    have hiw : i ≫ f = πY ≫ v ≫ U.ι := by
      rw [← Category.assoc, hv, IsOpenImmersion.lift_fac]
    have hcf : c' ≫ f = v ≫ U.ι := by
      rw [hc'i, Category.assoc, hiw, ← Category.assoc, hyπ, Category.id_comp]
    have hxh : x ≫ σ ≫ f = v ≫ U.ι := by
      rw [← Category.assoc, hσi, Category.assoc, hiw, ← Category.assoc, hy₀, Category.id_comp]
    have key := congrArg (fun m : Spec (.of K) ⟶ Z => m (IsLocalRing.closedPoint K))
      (hcf.trans hxh.symm)
    simpa only [Scheme.Hom.comp_apply, hc'apply, hxpt] using key.symm
  · rw [Category.assoc, hhZ, hf]

/-- The morphism `h` produced by the rigidity theorem
`AlgebraicGeometry.existsUnique_comp_fst_eq_of_isProper` is `σ ≫ f` for the section
`σ = (id, y₀) : X ⟶ X ×[K] Y` attached to any `K`-rational point `y₀` of `Y`. -/
theorem comp_fst_lift_comp_eq_of_isProper [IsAlgClosed K] (πX : X ⟶ Spec (.of K))
    (πY : Y ⟶ Spec (.of K)) (πZ : Z ⟶ Spec (.of K))
    [LocallyOfFiniteType πX] [GeometricallyIntegral πX]
    [IsProper πY] [GeometricallyIntegral πY]
    [IsSeparated πZ] [LocallyOfFiniteType πZ]
    (f : pullback πX πY ⟶ Z) (hf : f ≫ πZ = pullback.fst πX πY ≫ πX)
    (x₀ : X) (z₀ : Z) (hx₀ : ⇑f '' (⇑(pullback.fst πX πY) ⁻¹' {x₀}) = {z₀})
    (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) :
    pullback.fst πX πY ≫ pullback.lift (𝟙 X) (πX ≫ y₀) (by simp [hy₀]) ≫ f = f := by
  obtain ⟨h, hh, -⟩ := existsUnique_comp_fst_eq_of_isProper πX πY πZ f hf x₀ z₀ hx₀
  have hσ : pullback.lift (𝟙 X) (πX ≫ y₀) (by simp [hy₀]) ≫ f = h := by
    rw [← hh, ← Category.assoc, pullback.lift_fst, Category.id_comp]
  rw [hσ, hh]

end Rigidity

end AlgebraicGeometry
