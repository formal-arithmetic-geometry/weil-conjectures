/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.Rigidification

import Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed
import Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen

/-!
# The theorem of the cube

Let `X`, `Y` be proper and geometrically integral over a field `K`, let `Z` be connected, and
let `x`, `y`, `z` be `K`-points of `X`, `Y`, `Z`. An invertible module on `X ×_K Y ×_K Z` is
determined, up to isomorphism, by its restrictions to the three slices `{x} × Y × Z`,
`X × {y} × Z` and `X × Y × {z}` (Stacks, Tag 0BF4).

Products are taken in the cartesian monoidal category `Over (Spec K)`, so that
`((X ⊗ Y) ⊗ Z).left` is the fibre product `(X ×_K Y) ×_K Z`, and the slice inclusions are
written with `CartesianMonoidalCategory.lift`.

## Main statements

- `AlgebraicGeometry.nonempty_iso_of_nonempty_iso_overPullback_slices`: the theorem of the cube.

The proof follows Stacks: the locus of points of `Z` over which `M` and `N` are locally
isomorphic is open, closed (`AlgebraicGeometry.isClosed_setOf_exists_nonempty_iso_preimageSnd`)
and contains `z` (`AlgebraicGeometry.exists_mem_nonempty_iso_preimageSnd`), hence is all of the
connected scheme `Z`, and an isomorphism locally over `Z` globalises
(`AlgebraicGeometry.nonempty_iso_of_forall_exists_nonempty_iso_preimageSnd`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

variable {K : Type u} [Field K]

/-- The open subscheme `X ×_K Y ×_K U` of `X ×_K Y ×_K Z` lying over an open `U ⊆ Z`. -/
noncomputable abbrev preimageSnd (X Y Z : Over (Spec (.of K))) (U : Z.left.Opens) :
    ((X ⊗ Y) ⊗ Z).left.Opens :=
  (snd (X ⊗ Y) Z).left ⁻¹ᵁ U

private lemma pullback_iso_iff_tensor_dual_iso_unit {A B : Scheme.{u}} (g : A ⟶ B)
    (M N : B.Modules) [N.IsInvertible] :
    Nonempty ((Scheme.Modules.pullback g).obj M ≅ (Scheme.Modules.pullback g).obj N) ↔
      Nonempty ((Scheme.Modules.pullback g).obj (M ⊗ Nᵛ) ≅ 𝟙_ A.Modules) := by
  constructor
  · rintro ⟨e⟩
    exact nonempty_pullback_tensorObj_dual_iso_unit g M N e
  · rintro ⟨e⟩
    let F := Scheme.Modules.pullback g
    obtain ⟨t⟩ := nonempty_pullback_tensorObj_iso g M Nᵛ
    obtain ⟨d⟩ := nonempty_pullback_tensorObj_dual_iso_unit g N N (Iso.refl _)
    obtain ⟨t'⟩ := nonempty_pullback_tensorObj_iso g N Nᵛ
    let ev : F.obj N ⊗ F.obj Nᵛ ≅ 𝟙_ A.Modules := t'.symm ≪≫ d
    exact ⟨(ρ_ (F.obj M)).symm ≪≫
      (Iso.refl _ ⊗ᵢ ((β_ _ _) ≪≫ ev).symm) ≪≫ (α_ _ _ _).symm ≪≫
      ((t.symm ≪≫ e) ⊗ᵢ Iso.refl _) ≪≫ λ_ (F.obj N)⟩

private lemma nonempty_pullback_fiber_iso_unit_of_open {P S : Scheme.{u}}
    (f : P ⟶ S) (L : P.Modules) (s : S) (U : S.Opens) (hs : s ∈ U)
    (e : Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L ≅
      SheafOfModules.unit _)) :
    Nonempty ((Scheme.Modules.pullback (f.fiberι s)).obj L ≅ SheafOfModules.unit _) := by
  have hsub : Set.range (f.fiberι s) ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [f.range_fiberι, Scheme.Opens.range_ι]
    intro p hp
    change f p ∈ U
    have hp' : f p = s := hp
    rwa [hp']
  let j := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (f.fiberι s) hsub
  have hj : j ≫ (f ⁻¹ᵁ U).ι = f.fiberι s := IsOpenImmersion.lift_fac _ _ _
  exact ⟨(pullbackCongr hj.symm).app L ≪≫ (pullbackComp j _).symm.app L ≪≫
    (Scheme.Modules.pullback j).mapIso e.some ≪≫ pullbackObjUnitIso j⟩

private lemma geometricallyIntegral_tensorHom (X Y : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [GeometricallyIntegral Y.hom] :
    GeometricallyIntegral (X ⊗ Y).hom := by
  refine ⟨?_⟩
  intro k _ t P a b H
  let e := pullbackRightPullbackFstIso X.hom t (pullback.fst X.hom Y.hom)
  have : IsIntegral (pullback X.hom t) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  have : IsLocallyNoetherian (pullback X.hom t) := inferInstance
  have : IsIntegral (pullback (pullback.fst X.hom Y.hom) (pullback.fst X.hom t)) :=
    inferInstance
  have : Nonempty P := ⟨H.isoPullback.inv (e.hom (Nonempty.some inferInstance))⟩
  exact isIntegral_of_isOpenImmersion (H.isoPullback.hom ≫ e.inv)

/-- **Closedness of the locus of triviality** (Stacks, Tags 0BDP, 0BF0 and 0BF3).

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `M`, `N` be invertible modules on `X ×_K Y ×_K Z` which become isomorphic on the slices
`{x} × Y × Z` and `X × {y} × Z`. Then the set of points `t ∈ Z` having an open neighbourhood
`U` with `M ≅ N` on `X ×_K Y ×_K U` is closed.

By Tag 0BF3 (applied over `Z`, using the two slices) this set is the set of `t` such that `M` and
`N` are isomorphic on the fibre over `t`, and by Tags 0BDP and 0BF0 that set is the image of a
closed immersion `Z' → Z`.
(blueprint: lem-sc-cube-local-isomorphism-closed). -/
theorem isClosed_setOf_exists_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N)) :
    IsClosed {t : Z.left | ∃ U : Z.left.Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N)} := by
  let p := (snd (X ⊗ Y) Z).left
  let L := M ⊗ Nᵛ
  have : GeometricallyIntegral (X ⊗ Y).hom := geometricallyIntegral_tensorHom X Y
  have : IsProper (X ⊗ Y).hom := by
    change IsProper (pullback.fst X.hom Y.hom ≫ X.hom)
    infer_instance
  have : IsProper p := inferInstanceAs (IsProper (pullback.snd (X ⊗ Y).hom Z.hom))
  have : Flat p := inferInstanceAs (Flat (pullback.snd (X ⊗ Y).hom Z.hom))
  have : LocallyOfFinitePresentation p :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd (X ⊗ Y).hom Z.hom))
  have : GeometricallyIntegral p :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd (X ⊗ Y).hom Z.hom))
  let σ := lift (lift (toUnit Z ≫ x) (toUnit Z ≫ y)) (𝟙 Z)
  have hσ : σ.left ≫ p = 𝟙 Z.left := by
    rw [← Over.comp_left]
    simp [σ]
  have hclosed := Scheme.isClosed_setOf_nonempty_pullback_fiber_iso_unit p σ.left hσ L
  have hset : {t : Z.left | ∃ U : Z.left.Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N)} =
      {t : Z.left | Nonempty ((Scheme.Modules.pullback (p.fiberι t)).obj L ≅
        SheafOfModules.unit _)} := by
    ext t
    constructor
    · rintro ⟨U, ht, e⟩
      exact nonempty_pullback_fiber_iso_unit_of_open p L t U ht
        ((pullback_iso_iff_tensor_dual_iso_unit _ M N).mp e)
    · intro ht
      obtain ⟨U, htU, e⟩ := exists_mem_nonempty_pullback_iso_unit_of_cube_fiber X Y Z x y L
        ((pullback_iso_iff_tensor_dual_iso_unit _ M N).mp hx)
        ((pullback_iso_iff_tensor_dual_iso_unit _ M N).mp hy) t ht
      exact ⟨U, htU, (pullback_iso_iff_tensor_dual_iso_unit _ M N).mpr e⟩
  rw [hset]
  exact hclosed


private lemma rationalPoint_fromSpecResidueField_factor (Z : Over (Spec (.of K)))
    (z : 𝟙_ _ ⟶ Z) :
    Z.left.fromSpecResidueField (z.left (IsLocalRing.closedPoint K)) ≫ Z.hom ≫ z.left =
      Z.left.fromSpecResidueField (z.left (IsLocalRing.closedPoint K)) := by
  let t := z.left (IsLocalRing.closedPoint K)
  let a := Z.left.descResidueField (Scheme.stalkClosedPointTo z.left)
  let r := Z.left.fromSpecResidueField t ≫ Z.hom
  have ha : Spec.map a ≫ Z.left.fromSpecResidueField t = z.left :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z.left z.left
  have hw : z.left ≫ Z.hom = 𝟙 _ := z.w
  have hba : Spec.preimage r ≫ a = 𝟙 _ := by
    apply Spec.map_injective
    simp only [Spec.map_comp, Spec.map_preimage, Spec.map_id]
    change Spec.map a ≫ (Z.left.fromSpecResidueField t ≫ Z.hom) = _
    rw [← Category.assoc, ha, hw]
    rfl
  have hsurj : Function.Surjective a.hom := by
    intro k
    refine ⟨(Spec.preimage r).hom k, ?_⟩
    exact congrArg (fun f ↦ f.hom k) hba
  have : IsIso a := (ConcreteCategory.isIso_iff_bijective a).mpr ⟨a.hom.injective, hsurj⟩
  have : IsIso (Spec.map a) := inferInstance
  apply (cancel_epi (Spec.map a)).mp
  rw [← Category.assoc, ← Category.assoc, ha, hw]
  change (𝟙 (Spec (.of K))) ≫ z.left = z.left
  simp

/-- **Openness of the locus of triviality at a rational point** (Stacks, Tag 0BF3).

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `z` be a `K`-point of `Z`. If two invertible modules `M`, `N` on `X ×_K Y ×_K Z` become
isomorphic on the slices `{x} × Y × Z`, `X × {y} × Z` and `X × Y × {z}`, then they are
isomorphic on `X ×_K Y ×_K U` for some open neighbourhood `U` of `z`.

Tag 0BF3 is applied over the base `Z` to `X ×_K Z` and `Y ×_K Z` with the sections given by `x`
and `y`; its proof is an infinitesimal lifting argument based on the injectivity of
`H¹(X × Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` (Künneth).
(blueprint: lem-sc-cube-rational-neighborhood). -/
theorem exists_mem_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (z : 𝟙_ _ ⟶ Z) (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N))
    (hz : Nonempty (overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) M ≅
      overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) N)) :
    ∃ U : Z.left.Opens, z.left.base (IsLocalRing.closedPoint K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N) := by
  let L := M ⊗ Nᵛ
  let p := (snd (X ⊗ Y) Z).left
  let t := z.left (IsLocalRing.closedPoint K)
  let i := lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)
  let q := p.fiberι t ≫ (fst (X ⊗ Y) Z).left
  have hqi : q ≫ i.left = p.fiberι t := by
    apply pullback.hom_ext
    · simp [q, i]
    · change (q ≫ i.left) ≫ (snd (X ⊗ Y) Z).left = _
      rw [Category.assoc, ← Over.comp_left]
      simp only [i, lift_snd, Over.comp_left]
      change (p.fiberι t ≫ pullback.fst (X ⊗ Y).hom Z.hom) ≫
        (X ⊗ Y).hom ≫ z.left = p.fiberι t ≫ pullback.snd (X ⊗ Y).hom Z.hom
      rw [Category.assoc, pullback.condition_assoc]
      change p.fiberι t ≫ p ≫ Z.hom ≫ z.left = p.fiberι t ≫ p
      rw [← Category.assoc, Scheme.Hom.fiber_fac]
      simp only [Category.assoc]
      rw [rationalPoint_fromSpecResidueField_factor Z z]
  have ht : Nonempty ((Scheme.Modules.pullback (p.fiberι t)).obj L ≅
      SheafOfModules.unit _) := by
    obtain ⟨e⟩ := (pullback_iso_iff_tensor_dual_iso_unit i.left M N).mp hz
    exact ⟨(pullbackCongr hqi.symm).app L ≪≫ (pullbackComp q i.left).symm.app L ≪≫
      (Scheme.Modules.pullback q).mapIso e ≪≫ pullbackObjUnitIso q⟩
  obtain ⟨U, htU, e⟩ := exists_mem_nonempty_pullback_iso_unit_of_cube_fiber X Y Z x y L
    ((pullback_iso_iff_tensor_dual_iso_unit _ M N).mp hx)
    ((pullback_iso_iff_tensor_dual_iso_unit _ M N).mp hy) t ht
  exact ⟨U, htU, (pullback_iso_iff_tensor_dual_iso_unit _ M N).mpr e⟩


/-- **Invertible modules isomorphic locally over the base are isomorphic** (Stacks, Tag 0BDP and
the last step of the proof of Tag 0BF4).

Let `X`, `Y` be proper and geometrically integral over a field `K` and let `x` be a `K`-point of
`X`. If two invertible modules `M`, `N` on `X ×_K Y ×_K Z` are isomorphic on `X ×_K Y ×_K U` for
the members `U` of an open cover of `Z`, and are isomorphic on the slice `{x} × Y × Z`, then
`M ≅ N`.

We show that `L = M ⊗ Nᵛ` is trivial. Let `π : X ×_K (Y ×_K Z) ⟶ Y ×_K Z` be the projection and
`σ` the slice `{x} × Y × Z`, a section of `π`. As `X` is proper and geometrically integral, `π`
induces bijections `Γ(V, 𝒪) ≅ Γ(π⁻¹ V, 𝒪)` on all opens `V`. Local generators of `L` over the
opens `π⁻¹ V`, `V` lying over an open of the cover of `Z`, can be rescaled so that their
pullbacks along `σ` agree with a fixed generator of `σ^* L ≅ 𝒪`; they then agree on overlaps and
glue (`AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator_top_of_comp_eq_id`). -/
theorem nonempty_iso_of_forall_exists_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X)
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hloc : ∀ t : Z.left, ∃ U : Z.left.Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N))
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N)) :
    Nonempty (M ≅ N) := by
  let : X.left.Over (Spec (.of K)) := ⟨X.hom⟩
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : Scheme.GlobalSectionsBijective K X.left :=
    have : IsProper (X.left ↘ Spec (.of K)) := inferInstanceAs (IsProper X.hom)
    have : GeometricallyIntegral (X.left ↘ Spec (.of K)) :=
      inferInstanceAs (GeometricallyIntegral X.hom)
    .of_geometricallyIntegral (k := K) (X := X.left)
  -- The slice `σ : Y × Z ⟶ X × Y × Z` at `x` is a section of the projection `π`.
  set σ := lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)
  let π : ((X ⊗ Y) ⊗ Z).left ⟶ (Y ⊗ Z).left := ((α_ X Y Z).hom ≫ snd X (Y ⊗ Z)).left
  have hσ : σ.left ≫ π = 𝟙 _ := by
    rw [← Over.comp_left]
    have : σ ≫ (α_ X Y Z).hom ≫ snd X (Y ⊗ Z) = 𝟙 _ := by simp [σ]
    rw [this]
    rfl
  have hπq : π ≫ (snd Y Z).left = (snd (X ⊗ Y) Z).left := by
    rw [← Over.comp_left]
    congr 1
    simp
  -- `π` is the base change of `X ⟶ Spec K`, so it induces bijections on sections.
  have H : IsPullback ((α_ X Y Z).hom ≫ fst X (Y ⊗ Z)).left π (X.left ↘ Spec (.of K))
      (Y ⊗ Z).hom := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso (α_ X Y Z)) rfl rfl
    change _ ≫ X.hom = _ ≫ (Y ⊗ Z).hom
    rw [Over.w, Over.w]
  have hπ (V : (Y ⊗ Z).left.Opens) : Function.Surjective (π.app V) :=
    (Scheme.Hom.bijective_app_of_comp_eq_id π σ.left hσ (fun _ hA ↦
      Scheme.GlobalSectionsBijective.isIso_app_of_isPullback H hA) V).2
  -- `L = M ⊗ Nᵛ` is trivial over the opens `π⁻¹ q⁻¹ U` and on the slice.
  choose U hU e using hloc
  have hV : ⨆ t, (snd Y Z).left ⁻¹ᵁ U t = ⊤ :=
    eq_top_iff.2 fun b _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨_, hU ((snd Y Z).left b)⟩
  have hgen (t : Z.left) :
      ∃ m : Γ(M ⊗ Nᵛ, π ⁻¹ᵁ ((snd Y Z).left ⁻¹ᵁ U t)), IsFreeGenerator m := by
    obtain ⟨d⟩ := nonempty_pullback_tensorObj_dual_iso_unit _ M N (e t).some
    obtain ⟨m, hm⟩ := exists_isFreeGenerator_of_pullback_ι_iso _ _ d
    have hO : π ⁻¹ᵁ ((snd Y Z).left ⁻¹ᵁ U t) = preimageSnd X Y Z (U t) := by
      rw [← Scheme.Hom.comp_preimage, hπq]
    exact ⟨_, hm.map hO.le⟩
  choose m hm using hgen
  obtain ⟨d⟩ := nonempty_pullback_tensorObj_dual_iso_unit σ.left M N hx.some
  obtain ⟨g, hg⟩ := exists_isFreeGenerator_top_of_comp_eq_id π σ.left hσ hπ (M ⊗ Nᵛ) _ hV m hm
    ((isFreeGenerator_one ⊤).app_hom d.symm)
  have := isIso_homOfGlobalSection hg
  exact nonempty_iso_of_tensorObj_dual_iso_unit M N (asIso (homOfGlobalSection _ g)).symm

/-- **The theorem of the cube** (Stacks, Tag 0BF4, over `S = Spec K` with `K`-rational points).

Let `X`, `Y` be proper and geometrically integral over a field `K`, let `Z` be a connected
`K`-scheme and let `x`, `y`, `z` be `K`-points of `X`, `Y`, `Z`. If two invertible modules `M`,
`N` on `X ×_K Y ×_K Z` become isomorphic on each of the three slices `{x} × Y × Z`,
`X × {y} × Z` and `X × Y × {z}`, then `M ≅ N`.

Stacks states this for one invertible module `L` (if `L` is trivial on the three slices then
`L` is trivial); the form here follows by applying it to `L = M ⊗ N⁻¹`. Over a field the
flatness and finite presentation hypotheses of Tag 0BF4 are automatic. -/
theorem nonempty_iso_of_nonempty_iso_overPullback_slices (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] [ConnectedSpace Z.left] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (z : 𝟙_ _ ⟶ Z) (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N))
    (hz : Nonempty (overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) M ≅
      overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) N)) :
    Nonempty (M ≅ N) := by
  -- The set of points of `Z` over which `M` and `N` are locally isomorphic is open by
  -- definition, closed and contains `z`, hence is all of `Z`.
  set T : Set Z.left := {t | ∃ U : Z.left.Opens, t ∈ U ∧
    Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
      (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N)} with hT
  have hopen : IsOpen T := isOpen_iff_forall_mem_open.2 fun _ ⟨U, htU, e⟩ =>
    ⟨U, fun _ ht' => ⟨U, ht', e⟩, U.isOpen, htU⟩
  have hclosed : IsClosed T :=
    isClosed_setOf_exists_nonempty_iso_preimageSnd X Y Z x y M N hx hy
  have hmem : z.left.base (IsLocalRing.closedPoint K) ∈ T :=
    exists_mem_nonempty_iso_preimageSnd X Y Z x y z M N hx hy hz
  have huniv : T = Set.univ :=
    (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨_, hmem⟩)
  exact nonempty_iso_of_forall_exists_nonempty_iso_preimageSnd X Y Z x M N
    (fun t => show t ∈ T from huniv ▸ Set.mem_univ t) hx

end AlgebraicGeometry
