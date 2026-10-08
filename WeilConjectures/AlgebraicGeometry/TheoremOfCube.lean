/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

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

section Sections

/-- **Flat base change of `H⁰(X, 𝒪_X) = k` over an affine open.** Let `X` be a quasi-compact
quasi-separated `k`-scheme with `H⁰(X, 𝒪_X) = k`, and let `P = X ×_k B` be a base change of `X`.
Then for every affine open `A ⊆ B` the projection `π : P ⟶ B` induces an isomorphism
`Γ(B, A) ≅ Γ(P, π⁻¹ A)`: by flat base change, `Γ(P, π⁻¹ A) = Γ(X, 𝒪_X) ⊗_k Γ(B, A)`. -/
theorem Scheme.GlobalSectionsBijective.isIso_app_of_isPullback (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [CompactSpace X] [QuasiSeparatedSpace X]
    [Scheme.GlobalSectionsBijective k X] {P B : Scheme.{u}} {ρ : P ⟶ X} {π : P ⟶ B}
    {g : B ⟶ Spec (.of k)} (H : IsPullback ρ π (X ↘ Spec (.of k)) g) {A : B.Opens}
    (hA : IsAffineOpen A) : IsIso (π.app A) := by
  have hUY : π ⁻¹ᵁ A = ρ ⁻¹ᵁ ⊤ ⊓ π ⁻¹ᵁ A := by simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := A)
    (UX := ⊤) le_top le_top hUY (isAffineOpen_top _) hA isCompact_univ isQuasiSeparated_univ
  have hpush := (isIso_pushoutSection_iff _ _ _ _).mp hiso
  have hX : IsIso ((X ↘ Spec (.of k)).appLE ⊤ ⊤ le_top) := by
    have h := Scheme.GlobalSectionsBijective.bijective_globalSectionsRingHom (k := k) (X := X)
    rw [Scheme.globalSectionsRingHom, ← ConcreteCategory.isIso_iff_bijective] at h
    have : IsIso (X ↘ Spec (.of k)).appTop :=
      IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv _
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using this
  have := hpush.isIso_inr_of_isIso
  rw [Scheme.Hom.app_eq_appLE]
  exact this

/-- If `π : P ⟶ B` has a section `σ` and `π` induces isomorphisms `Γ(B, A) ≅ Γ(P, π⁻¹ A)` on
affine opens `A`, then it induces bijections `Γ(B, V) ≅ Γ(P, π⁻¹ V)` on all opens `V`. -/
theorem Scheme.Hom.bijective_app_of_comp_eq_id {P B : Scheme.{u}} (π : P ⟶ B) (σ : B ⟶ P)
    (hσ : σ ≫ π = 𝟙 B) (h : ∀ A : B.Opens, IsAffineOpen A → IsIso (π.app A)) (V : B.Opens) :
    Function.Bijective (π.app V) := by
  have hle (W : B.Opens) : W ≤ σ ⁻¹ᵁ π ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, hσ]
    exact le_rfl
  have gen (f : B ⟶ B) (hf : f = 𝟙 B) (W : B.Opens) (hW : W ≤ f ⁻¹ᵁ W) (a : Γ(B, W)) :
      B.presheaf.map (homOfLE hW).op (f.app W a) = a := by
    subst hf
    exact Scheme.presheaf_map_id_apply _ a
  have key (W : B.Opens) (a : Γ(B, W)) :
      B.presheaf.map (homOfLE (hle W)).op (σ.app _ (π.app W a)) = a :=
    gen (σ ≫ π) hσ W (hle W) a
  refine ⟨fun a b hab ↦ by rw [← key V a, ← key V b, hab], fun f ↦ ?_⟩
  refine ⟨B.presheaf.map (homOfLE (hle V)).op (σ.app _ f), ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' P.sheaf
    (fun A : {A : B.Opens // IsAffineOpen A ∧ A ≤ V} ↦ π ⁻¹ᵁ A.1) (π ⁻¹ᵁ V)
    (fun A ↦ homOfLE (π.preimage_mono A.2.2)) ?_ _ _ fun A ↦ ?_
  · intro x hx
    obtain ⟨A, hA, hxA, hAV⟩ := exists_isAffineOpen_mem_and_subset (x := π x) (U := V) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨A, hA, hAV⟩, hxA⟩
  · have := h A.1 A.2.1
    obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso (π.app A.1)).2
      (P.presheaf.map (homOfLE (π.preimage_mono A.2.2)).op f)
    change P.presheaf.map _ (π.app V _) = P.presheaf.map _ f
    have e1 (y : Γ(B, V)) : P.presheaf.map (homOfLE (π.preimage_mono A.2.2)).op (π.app V y) =
        π.app A.1 (B.presheaf.map (homOfLE A.2.2).op y) :=
      (ConcreteCategory.congr_hom (π.naturality (homOfLE A.2.2).op) y).symm
    have e2 : σ.app (π ⁻¹ᵁ A.1) (P.presheaf.map (homOfLE (π.preimage_mono A.2.2)).op f) =
        B.presheaf.map (homOfLE (σ.preimage_mono (π.preimage_mono A.2.2))).op
          (σ.app (π ⁻¹ᵁ V) f) :=
      ConcreteCategory.congr_hom (σ.naturality (homOfLE (π.preimage_mono A.2.2)).op) f
    rw [e1, ← hb]
    congr 1
    rw [← key A.1 b, hb, e2]
    simp only [← ConcreteCategory.comp_apply]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    rfl

end Sections

section FreeGenerator

/-- A section whose restrictions to the members of an open cover are free generators is a free
generator. -/
lemma Scheme.Modules.IsFreeGenerator.of_iSup {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (e : Γ(M, U)) {ι : Type*} (W : ι → X.Opens) (hW : ∀ i, W i ≤ U) (hcov : U ≤ ⨆ i, W i)
    (h : ∀ i, IsFreeGenerator (M.presheaf.map (homOfLE (hW i)).op e)) : IsFreeGenerator e := by
  let S : Sieve U := ⟨fun {V} _ ↦ ∃ i, V ≤ W i, fun ⟨i, hi⟩ g ↦ ⟨i, (leOfHom g).trans hi⟩⟩
  refine isFreeGenerator_of_mem e (S := S) (fun x hx ↦ ?_) fun V f ⟨i, hi⟩ ↦ ?_
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hx)
    exact ⟨W i, homOfLE (hW i), ⟨i, le_rfl⟩, hi⟩
  · have := (h i).map hi
    rw [presheaf_map_map_apply] at this
    rwa [Subsingleton.elim f (homOfLE hi ≫ homOfLE (hW i))]

/-- **Rigidified local generators glue.** Let `π : P ⟶ B` be a morphism with a section `σ` such
that `π` induces surjections `Γ(B, V) ⟶ Γ(P, π⁻¹ V)` for all opens `V`. Let `L` be an
`𝒪_P`-module with free generators on the members `π⁻¹ V i` of an open cover pulled back from
`B`, and such that `σ^* L` has a global free generator `γ`. Then `L` has a global free
generator.

After multiplying each generator `e i` by a unit pulled back from `B`, we may assume that
`σ^* (e i) = γ`. Two such generators differ on overlaps by a unit `w = π^♯ a`; pulling back along
`σ` shows `a = σ^♯ π^♯ a = 1`, so the generators agree on overlaps and glue. -/
theorem Scheme.Modules.exists_isFreeGenerator_top_of_comp_eq_id {P B : Scheme.{u}} (π : P ⟶ B)
    (σ : B ⟶ P) (hσ : σ ≫ π = 𝟙 B) (hπ : ∀ V : B.Opens, Function.Surjective (π.app V))
    (L : P.Modules) {ι : Type*} (V : ι → B.Opens) (hV : ⨆ i, V i = ⊤)
    (e : ∀ i, Γ(L, π ⁻¹ᵁ V i)) (he : ∀ i, IsFreeGenerator (e i))
    {γ : Γ((Scheme.Modules.pullback σ).obj L, ⊤)} (hγ : IsFreeGenerator γ) :
    ∃ g : Γ(L, ⊤), IsFreeGenerator g := by
  have hle (W : B.Opens) : W ≤ σ ⁻¹ᵁ π ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, hσ]
    exact le_rfl
  have hge (W : B.Opens) : σ ⁻¹ᵁ π ⁻¹ᵁ W ≤ W := by
    rw [← Scheme.Hom.comp_preimage, hσ]
    exact le_rfl
  have gen (f : B ⟶ B) (hf : f = 𝟙 B) (W W' : B.Opens) (hW : W' ≤ f ⁻¹ᵁ W) (hW' : W' ≤ W)
      (a : Γ(B, W)) : B.presheaf.map (homOfLE hW).op (f.app W a) =
        B.presheaf.map (homOfLE hW').op a := by
    subst hf
    rfl
  have key (W W' : B.Opens) (hW : W' ≤ σ ⁻¹ᵁ π ⁻¹ᵁ W) (hW' : W' ≤ W) (a : Γ(B, W)) :
      B.presheaf.map (homOfLE hW).op (σ.app _ (π.app W a)) = B.presheaf.map (homOfLE hW').op a :=
    gen (σ ≫ π) hσ W W' hW hW' a
  -- Rigidify the generators along `σ`.
  have hs (i : ι) : IsFreeGenerator (pullbackSection σ (e i)) := (he i).pullback_unit_app σ
  choose u hu using fun i ↦ (hs i).exists_unit_smul_eq
    (hγ.map (le_top : σ ⁻¹ᵁ π ⁻¹ᵁ V i ≤ ⊤))
  let c (i : ι) : Γ(B, V i)ˣ :=
    Units.map (B.presheaf.map (homOfLE (hle (V i))).op).hom.toMonoidHom (u i)
  let e' (i : ι) : Γ(L, π ⁻¹ᵁ V i) := π.app (V i) (c i).1 • e i
  have he' (i : ι) : IsFreeGenerator (e' i) :=
    (he i).units_smul (Units.map (π.app (V i)).hom.toMonoidHom (c i))
  have hσe' (i : ι) : pullbackSection σ (e' i) =
      ((Scheme.Modules.pullback σ).obj L).presheaf.map
        (homOfLE (le_top : σ ⁻¹ᵁ π ⁻¹ᵁ V i ≤ ⊤)).op γ := by
    rw [pullbackSection_smul, hu i]
    congr 1
    have h1 := key (V i) _ le_rfl (hge _) (c i).1
    rw [Scheme.presheaf_map_id_apply] at h1
    rw [h1]
    change B.presheaf.map _ (B.presheaf.map _ _) = _
    rw [Scheme.presheaf_map_map_apply, Scheme.presheaf_map_id_apply]
  -- The rigidified generators agree on overlaps.
  have hcompat : TopCat.Presheaf.IsCompatible L.presheaf (fun i ↦ π ⁻¹ᵁ V i) e' := by
    intro i j
    have hri := (he' i).map (inf_le_left : π ⁻¹ᵁ V i ⊓ π ⁻¹ᵁ V j ≤ _)
    have hrj := (he' j).map (inf_le_right : π ⁻¹ᵁ V i ⊓ π ⁻¹ᵁ V j ≤ _)
    obtain ⟨w, hw⟩ := hri.exists_unit_smul_eq hrj
    have h2 := congrArg (pullbackSection σ) hw
    rw [pullbackSection_smul, pullbackSection_map, pullbackSection_map, hσe' i, hσe' j,
      presheaf_map_map_apply, presheaf_map_map_apply] at h2
    have hγO := hγ.map (le_top : σ ⁻¹ᵁ (π ⁻¹ᵁ V i ⊓ π ⁻¹ᵁ V j) ≤ ⊤)
    have h3 : σ.app _ w.1 = 1 := by
      refine hγO.smul_left_injective ?_
      dsimp only
      rw [one_smul]
      convert h2.symm using 3 <;> rfl
    obtain ⟨a, ha⟩ := hπ (V i ⊓ V j) w.1
    have ha1 : a = 1 := by
      have h4 := key (V i ⊓ V j) (V i ⊓ V j) (hle _) le_rfl a
      rw [Scheme.presheaf_map_id_apply] at h4
      rw [← h4]
      erw [ha, h3]
      exact map_one _
    have hw1 : w.1 = 1 := by
      rw [← ha, ha1]
      exact map_one _
    rw [hw1, one_smul] at hw
    exact hw.symm
  -- Glue them.
  have hcov : (⊤ : P.Opens) ≤ ⨆ i, π ⁻¹ᵁ V i := by
    intro x _
    have : π x ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨L.presheaf, L.isSheaf⟩
    (fun i ↦ π ⁻¹ᵁ V i) ⊤ (fun _ ↦ homOfLE le_top) hcov e' hcompat
  exact ⟨g, IsFreeGenerator.of_iSup g _ (fun _ ↦ le_top) hcov fun i ↦ (hg i).symm ▸ he' i⟩

end FreeGenerator


/-- The open subscheme `X ×_K Y ×_K U` of `X ×_K Y ×_K Z` lying over an open `U ⊆ Z`. -/
noncomputable abbrev preimageSnd (X Y Z : Over (Spec (.of K))) (U : Z.left.Opens) :
    ((X ⊗ Y) ⊗ Z).left.Opens :=
  (snd (X ⊗ Y) Z).left ⁻¹ᵁ U

/-- Isomorphic modules stay isomorphic after pulling back along a further morphism. -/
lemma nonempty_iso_pullback_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) {M N : C.Modules}
    (e : (Scheme.Modules.pullback g).obj M ≅ (Scheme.Modules.pullback g).obj N) :
    Nonempty ((Scheme.Modules.pullback (f ≫ g)).obj M ≅ (Scheme.Modules.pullback (f ≫ g)).obj N) :=
  ⟨(pullbackComp f g).symm.app M ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫
    (pullbackComp f g).app N⟩

/-- **Triviality on a fibre spreads out** (Stacks, Tag 0BF3).

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `M`, `N` be invertible modules on `X ×_K Y ×_K Z` which become isomorphic on the slices
`{x} × Y × Z` and `X × {y} × Z`. If `M` and `N` become isomorphic on the fibre
`X ×_K Y ×_K Spec F` over a point `φ : Spec F ⟶ Z` with values in a field `F`, then they are
isomorphic on `X ×_K Y ×_K U` for an open neighbourhood `U` of the image of `φ`.

This is Tag 0BF3 applied over the base `Z` to `X ×_K Z` and `Y ×_K Z` with the sections given
by `x` and `y`. Its proof is an infinitesimal lifting argument based on the injectivity of
`H¹(X × Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` (Künneth, Tag 0BF2). Tag 0BF3 asks for triviality on the
fibre over the residue field `κ(t)` of the image `t` of `φ`; this is equivalent to triviality
over `F`, since a morphism `Spec F ⟶ Z` factors through the locally closed subscheme of
Tag 0BDP if and only if `t` lies in it. -/
theorem exists_mem_nonempty_iso_preimageSnd_of_nonempty_iso_fiber (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N))
    {F : Type u} [Field F] (φ : Spec (.of F) ⟶ Z.left)
    (hφ : Nonempty
      ((Scheme.Modules.pullback (Limits.pullback.fst (snd (X ⊗ Y) Z).left φ)).obj M ≅
        (Scheme.Modules.pullback (Limits.pullback.fst (snd (X ⊗ Y) Z).left φ)).obj N)) :
    ∃ U : Z.left.Opens, φ.base (IsLocalRing.closedPoint F) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N) :=
  sorry

/-- **The locus of triviality on the fibres is closed** (Stacks, Tags 0BDP and 0BF0).

Let `X`, `Y` be proper and geometrically integral over a field `K`, and let `M`, `N` be
invertible modules on `X ×_K Y ×_K Z`. The set of points `t ∈ Z` such that `M` and `N` become
isomorphic on the fibre `X ×_K Y ×_K Spec κ(t)` is closed.

By Tag 0BDP, applied to `X ×_K Y ×_K Z → Z` (flat, proper, of finite presentation, with
`𝒪_T ≅ p_* 𝒪` universally since `X ×_K Y` is proper and geometrically integral) and the
invertible module `M ⊗ N⁻¹`, there is a locally closed subscheme `Z' ⊆ Z` through which a
morphism `T ⟶ Z` factors if and only if `M ⊗ N⁻¹` becomes a pullback from `T`. For `T` the
spectrum of a field this means that `M ≅ N` on the fibre, so the set is the underlying set of
`Z'`, which is closed by Tag 0BF0 since the geometric fibres are integral. -/
theorem isClosed_setOf_nonempty_iso_fiber (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible]
    [N.IsInvertible] :
    IsClosed {t : Z.left | Nonempty
      ((Scheme.Modules.pullback
          (Limits.pullback.fst (snd (X ⊗ Y) Z).left (Z.left.fromSpecResidueField t))).obj M ≅
        (Scheme.Modules.pullback
          (Limits.pullback.fst (snd (X ⊗ Y) Z).left (Z.left.fromSpecResidueField t))).obj N)} :=
  sorry

/-- If `M ≅ N` over an open `U ⊆ Z`, then `M ≅ N` on the fibre over every field-valued point
of `U`. -/
lemma nonempty_iso_fiber_of_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) {U : Z.left.Opens}
    (e : (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
      (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N)
    {F : Type u} [Field F] (φ : Spec (.of F) ⟶ Z.left) (hφ : φ.base (IsLocalRing.closedPoint F) ∈ U) :
    Nonempty
      ((Scheme.Modules.pullback (Limits.pullback.fst (snd (X ⊗ Y) Z).left φ)).obj M ≅
        (Scheme.Modules.pullback (Limits.pullback.fst (snd (X ⊗ Y) Z).left φ)).obj N) := by
  have H : Set.range (Limits.pullback.fst (snd (X ⊗ Y) Z).left φ) ⊆
      Set.range (preimageSnd X Y Z U).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (snd (X ⊗ Y) Z).left ((Limits.pullback.fst (snd (X ⊗ Y) Z).left φ) w) ∈ U
    rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply,
      Subsingleton.elim ((Limits.pullback.snd (snd (X ⊗ Y) Z).left φ) w)
        (IsLocalRing.closedPoint F)]
    exact hφ
  rw [← IsOpenImmersion.lift_fac _ _ H]
  exact nonempty_iso_pullback_comp _ _ e

/-- **Closedness of the locus of triviality** (Stacks, Tags 0BDP, 0BF0 and 0BF3).

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `M`, `N` be invertible modules on `X ×_K Y ×_K Z` which become isomorphic on the slices
`{x} × Y × Z` and `X × {y} × Z`. Then the set of points `t ∈ Z` having an open neighbourhood
`U` with `M ≅ N` on `X ×_K Y ×_K U` is closed.

By Tag 0BF3 (`AlgebraicGeometry.exists_mem_nonempty_iso_preimageSnd_of_nonempty_iso_fiber`)
this set is the set of `t` such that `M` and `N` are isomorphic on the fibre over `t`, which is
closed by Tags 0BDP and 0BF0 (`AlgebraicGeometry.isClosed_setOf_nonempty_iso_fiber`). -/
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
  convert isClosed_setOf_nonempty_iso_fiber X Y Z M N using 1
  ext t
  constructor
  · rintro ⟨U, htU, ⟨e⟩⟩
    refine nonempty_iso_fiber_of_nonempty_iso_preimageSnd X Y Z M N e _ ?_
    convert htU
    exact Scheme.fromSpecResidueField_apply _ _
  · intro ht
    obtain ⟨U, htU, e⟩ :=
      exists_mem_nonempty_iso_preimageSnd_of_nonempty_iso_fiber X Y Z x y M N hx hy _ ht
    refine ⟨U, ?_, e⟩
    convert htU
    exact (Scheme.fromSpecResidueField_apply _ _).symm

/-- **Openness of the locus of triviality at a rational point** (Stacks, Tag 0BF3).

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `z` be a `K`-point of `Z`. If two invertible modules `M`, `N` on `X ×_K Y ×_K Z` become
isomorphic on the slices `{x} × Y × Z`, `X × {y} × Z` and `X × Y × {z}`, then they are
isomorphic on `X ×_K Y ×_K U` for some open neighbourhood `U` of `z`.

The slice `X × Y × {z}` is the fibre over `z`, so this is
`AlgebraicGeometry.exists_mem_nonempty_iso_preimageSnd_of_nonempty_iso_fiber`. -/
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
  refine exists_mem_nonempty_iso_preimageSnd_of_nonempty_iso_fiber X Y Z x y M N hx hy
    (F := K) z.left ?_
  -- The fibre over `z` is the slice `X × Y × {z}`.
  have H : Limits.pullback.fst (snd (X ⊗ Y) Z).left z.left =
      (Limits.pullback.fst (snd (X ⊗ Y) Z).left z.left ≫ (fst (X ⊗ Y) Z).left) ≫
        (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)).left := by
    set pf := Limits.pullback.fst (snd (X ⊗ Y) Z).left z.left
    apply Over.tensorObj_ext
    · change pf ≫ (fst (X ⊗ Y) Z).left =
        (pf ≫ (fst (X ⊗ Y) Z).left) ≫ (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)).left ≫ (fst (X ⊗ Y) Z).left
      rw [← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
    · change pf ≫ (snd (X ⊗ Y) Z).left =
        (pf ≫ (fst (X ⊗ Y) Z).left) ≫ (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)).left ≫ (snd (X ⊗ Y) Z).left
      rw [← Over.comp_left, lift_snd, Over.comp_left, Limits.pullback.condition, ← Category.assoc,
        Over.toUnit_left]
      congr 1
      calc Limits.pullback.snd (snd (X ⊗ Y) Z).left z.left
          = Limits.pullback.snd (snd (X ⊗ Y) Z).left z.left ≫ z.left ≫ Z.hom := by
            rw [Over.w z]; exact (Category.comp_id _).symm
        _ = pf ≫ (snd (X ⊗ Y) Z).left ≫ Z.hom := by rw [← Limits.pullback.condition_assoc]
        _ = (pf ≫ (fst (X ⊗ Y) Z).left) ≫ (X ⊗ Y).hom := by
            rw [Over.w, Category.assoc, Over.w]
  rw [H]
  exact nonempty_iso_pullback_comp _ _ hz.some

/-- **Invertible modules isomorphic locally over the base are isomorphic** (Stacks, Tag 0BDP and
the last step of the proof of Tag 0BF4).

Let `X`, `Y` be proper and geometrically integral over a field `K` and let `x` be a `K`-point of
`X`. If two invertible modules `M`, `N` on `X ×_K Y ×_K Z` are isomorphic on `X ×_K Y ×_K U` for
the members `U` of an open cover of `Z`, and are isomorphic on the slice `{x} × Y × Z`, then
`M ≅ N`.

Since the pushforward of `𝒪` along `X ×_K Y ×_K Z → Z` is `𝒪_Z`, the invertible module
`L = M ⊗ N⁻¹`, being locally on `Z` trivial, is the pullback of the invertible module
`𝒩 = p_* L` on `Z`; pulling back along the section `x × y × id_Z` shows `𝒩 ≅ 𝒪_Z`. -/
theorem nonempty_iso_of_forall_exists_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X)
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hloc : ∀ t : Z.left, ∃ U : Z.left.Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N))
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N)) :
    Nonempty (M ≅ N) :=
  sorry

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
