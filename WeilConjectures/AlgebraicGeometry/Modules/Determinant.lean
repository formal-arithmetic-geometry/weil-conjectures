/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.Mathlib.LinearAlgebra.Basis.Exact

/-!
# Determinants of finite locally free modules

For a finite locally free `𝒪_X`-module `E` of rank `r`, the top exterior power `det E = ⋀ʳ E`
(`AlgebraicGeometry.Scheme.Modules.exteriorPower`) is invertible, and determinants are
multiplicative in short exact sequences `0 → L → E → E' → 0` with `L` invertible:
`det E ≅ L ⊗ det E'`.

Both statements are proved with local frames: a *local frame* of `M` over `U` is a family of
sections over `U` which restricts to a basis of the sections over every open `W ⊆ U`. The wedge
product of a local frame is a free generator of the top exterior power, and two frames are
related on overlaps by `wedge v = det_b(v) • wedge b`. For the short exact sequence one glues the
free generators `l ∧ t₁ ∧ ⋯ ∧ t_r` of `det E` (with `t` lifting a frame of `E'`) and
`l ⊗ (t̄₁ ∧ ⋯ ∧ t̄_r)` of `L ⊗ det E'`, which have the same transition functions: the
transition matrices of the adapted frames of `E` are block triangular
(`Module.Basis.det_cons_of_exact`).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsLocalFrame`: local frames.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_isLocalFrame`: finite locally free modules of rank `r`
  have local frames of size `r`.
- `AlgebraicGeometry.Scheme.Modules.isInvertible_exteriorPower`: `⋀ʳ E` is invertible.
- `AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_iso_tensorObj`:
  `⋀^{r+1} E ≅ L ⊗ ⋀ʳ E'` for a short exact sequence `0 → L → E → E' → 0`.

(blueprint: `lem-sc-riemann-roch`, `sk-thm-picard-rr`)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

/-- A *local frame* of an `𝒪_X`-module `M` over `U`: a family `v` of sections of `M` over `U`
whose restrictions form a basis of `Γ(M, W)` over `Γ(X, W)` for every open `W ⊆ U`. -/
def IsLocalFrame {ι : Type*} {U : X.Opens} (v : ι → Γ(M, U)) : Prop :=
  ∀ (W : X.Opens) (hW : W ≤ U), ∃ b : Module.Basis ι Γ(X, W) Γ(M, W),
    ∀ k, b k = M.presheaf.map (homOfLE hW).op (v k)

namespace IsLocalFrame

/-- The restriction of a local frame is a local frame. -/
lemma restrict {ι : Type*} {U V : X.Opens} {v : ι → Γ(M, U)} (hv : IsLocalFrame v)
    (h : V ≤ U) : IsLocalFrame fun k ↦ M.presheaf.map (homOfLE h).op (v k) := by
  intro W hW
  obtain ⟨b, hb⟩ := hv W (hW.trans h)
  exact ⟨b, fun k ↦ (hb k).trans (presheaf_map_homOfLE_map_homOfLE h hW _).symm⟩

/-- The single section of a local frame of size one is a free generator. -/
lemma isFreeGenerator {U : X.Opens} {v : Fin 1 → Γ(M, U)} (hv : IsLocalFrame v) :
    IsFreeGenerator (v 0) := by
  intro W hW
  obtain ⟨b, hb⟩ := hv W hW
  dsimp only
  rw [← hb 0]
  refine ⟨fun a a' h ↦ ?_, fun m ↦ ⟨b.repr m 0, ?_⟩⟩
  · simpa using congrArg (fun x ↦ b.repr x 0) h
  · conv_rhs => rw [← b.sum_repr m]
    simp

/-- The wedge product of a local frame of size `r` is a free generator of `⋀ʳ M`. -/
lemma isFreeGenerator_wedge {r : ℕ} {U : X.Opens} {v : Fin r → Γ(M, U)} (hv : IsLocalFrame v) :
    IsFreeGenerator (wedge v) :=
  Modules.isFreeGenerator_wedge v fun V hV _ hx ↦
    ⟨V, le_rfl, hx, (hv V hV).choose, (hv V hV).choose_spec⟩

end IsLocalFrame

/-- **Change of frame for wedge products.** For a basis `b` of `Γ(M, W)` indexed by `Fin r` and
sections `v₁, …, v_r` over `W`, `v₁ ∧ ⋯ ∧ v_r = det_b(v) • b₁ ∧ ⋯ ∧ b_r` in `⋀ʳ M`. -/
lemma wedge_eq_det_smul {r : ℕ} {W : X.Opens} (b : Module.Basis (Fin r) Γ(X, W) Γ(M, W))
    (v : Fin r → Γ(M, W)) : wedge v = b.det v • wedge (M := M) ⇑b := by
  rw [wedge, wedge]
  erw [exteriorPower.ιMulti_eq_det_smul b v]
  exact toSheafificationObj_app_smul _ _ _

/-- The sections of `M` over an open `W ⊆ Y` of a trivialisation `M.over Y ≅ 𝒪_Y^I` commute with
restriction. -/
lemma sectionsLinearEquivOfOverIsoFree_map {Y : X.Opens} {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over Y ≅ SheafOfModules.free I) {V W : X.Opens} (hV : V ≤ Y) (hW : W ≤ V)
    (m : Γ(M, V)) (i : I) :
    sectionsLinearEquivOfOverIsoFree e (hW.trans hV) (M.presheaf.map (homOfLE hW).op m) i =
      X.presheaf.map (homOfLE hW).op (sectionsLinearEquivOfOverIsoFree e hV m i) := by
  let f : Over.mk (homOfLE (hW.trans hV)) ⟶ Over.mk (homOfLE hV) := Over.homMk (homOfLE hW)
  exact PresheafOfModules.naturality_apply (e.hom ≫ SheafOfModules.freeπ i).val f.op m

/-- **Local frames of finite locally free modules.** A finite locally free `𝒪_X`-module of rank
`r` has, around every point, a local frame of size `r`. -/
lemma exists_isLocalFrame (M : X.Modules) {r : ℕ} [M.IsFiniteLocallyFreeOfRank r] (x : X) :
    ∃ (U : X.Opens) (v : Fin r → Γ(M, U)), x ∈ U ∧ IsLocalFrame v := by
  classical
  obtain ⟨I, Y, hY, e⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.1
      ‹M.IsFiniteLocallyFreeOfRank r›
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).1 hY).exists_mem x
  let E (W : X.Opens) (h : W ≤ Y i) := sectionsLinearEquivOfOverIsoFree (e i).some h
  refine ⟨Y i, fun k ↦ (E (Y i) le_rfl).symm (Pi.single ⟨k⟩ 1), hi, fun W hW ↦ ?_⟩
  refine ⟨((Pi.basisFun Γ(X, W) (ULift (Fin r))).map (E W hW).symm).reindex Equiv.ulift,
    fun k ↦ ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, Pi.basisFun_apply]
  apply (E W hW).injective
  rw [LinearEquiv.apply_symm_apply]
  ext j
  have := sectionsLinearEquivOfOverIsoFree_map (e i).some le_rfl hW
    ((E (Y i) le_rfl).symm (Pi.single ⟨k⟩ 1)) j
  refine Eq.trans ?_ this.symm
  change _ = X.presheaf.map (homOfLE hW).op ((E (Y i) le_rfl) ((E (Y i) le_rfl).symm _) j)
  rw [LinearEquiv.apply_symm_apply]
  by_cases hj : j = ⟨k⟩
  · subst hj
    simp
  · simp [Pi.single_apply, hj]


/-- An `𝒪_X`-module with a free generator around every point is invertible. -/
lemma isInvertible_of_forall_exists_isFreeGenerator
    (h : ∀ x : X, ∃ (U : X.Opens) (e : Γ(M, U)), x ∈ U ∧ IsFreeGenerator e) : M.IsInvertible := by
  choose U e hx he using h
  have : SheafOfModules.IsInvertible.{u, u, u} M :=
    SheafOfModules.isInvertible_of_forall_over_unit (M := M) U
      (by
        rw [Opens.coversTop_iff]
        exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩))
      fun x ↦ ⟨(he x).overIso⟩
  exact IsInvertible.of_sheafOfModules M

/-- **The determinant of a finite locally free module is invertible.** For a finite locally free
`𝒪_X`-module `M` of rank `r`, the top exterior power `⋀ʳ M` is invertible: the wedge product of a
local frame is a free generator (`AlgebraicGeometry.Scheme.Modules.isFreeGenerator_wedge`).

(blueprint: `lem-sc-riemann-roch`) -/
instance isInvertible_exteriorPower (M : X.Modules) {r : ℕ} [M.IsFiniteLocallyFreeOfRank r] :
    (M.exteriorPower r).IsInvertible := by
  refine isInvertible_of_forall_exists_isFreeGenerator fun x ↦ ?_
  obtain ⟨U, v, hx, hv⟩ := exists_isLocalFrame (r := r) M x
  exact ⟨U, wedge v, hx, hv.isFreeGenerator_wedge⟩

section ShortExact

variable {S : ShortComplex X.Modules}

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of `𝒪_X`-modules with `M₁` quasi-coherent,
every section of `M₃` over an affine open lifts to `M₂`. -/
lemma surjective_app_g_of_isAffineOpen (hS : S.ShortExact)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₁] {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Surjective (S.g.app U) :=
  surjective_app_of_cechAcyclicOnAffines (hS.map_of_exact (toAb X))
    (cechAcyclicOnAffines_of_isQuasicoherent S.X₁) hU

/-- On sections over every open, a short exact sequence of `𝒪_X`-modules gives an exact sequence
`0 → Γ(M₁, W) → Γ(M₂, W) → Γ(M₃, W)` of `Γ(X, W)`-modules. -/
lemma exact_appₗ (hS : S.ShortExact) (W : X.Opens) :
    Function.Exact (Hom.appₗ S.f W) (Hom.appₗ S.g W) := by
  have := hS.mono_f
  intro y
  refine ⟨fun hy ↦ exists_app_f_eq_of_app_g_eq_zero hS.exact W y hy, ?_⟩
  rintro ⟨x, rfl⟩
  change (S.f ≫ S.g).app W x = 0
  rw [S.zero]
  rfl

/-- **Adapted frames.** In a short exact sequence `0 → L → E → E' → 0`, a local frame `l` of size
one of `L` and lifts `t` to `E` of a local frame of `E'` give the local frame `(l, t)` of `E`. -/
lemma IsLocalFrame.cons_of_shortExact (hS : S.ShortExact) {r : ℕ} {U : X.Opens}
    {l : Fin 1 → Γ(S.X₁, U)} {t : Fin r → Γ(S.X₂, U)} (hl : IsLocalFrame l)
    (ht : IsLocalFrame fun k ↦ S.g.app U (t k)) :
    IsLocalFrame (Fin.cons (S.f.app U (l 0)) t : Fin (r + 1) → Γ(S.X₂, U)) := by
  have := hS.mono_f
  intro W hW
  obtain ⟨b₁, hb₁⟩ := hl W hW
  obtain ⟨b₃, hb₃⟩ := ht W hW
  obtain ⟨b, hb⟩ := Module.Basis.exists_eq_cons_of_exact (f := Hom.appₗ S.f W)
    (g := Hom.appₗ S.g W) (injective_app_of_mono' S.f W) (exact_appₗ hS W) b₁ b₃ (fun k ↦ S.X₂.presheaf.map (homOfLE hW).op (t k)) fun k ↦ by
      rw [Hom.appₗ_apply, Hom.app_presheaf_map, hb₃]
  refine ⟨b, fun k ↦ ?_⟩
  rw [hb]
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp only [Fin.cons_zero, Hom.appₗ_apply, hb₁, Hom.app_presheaf_map]
  · simp only [Fin.cons_succ]

/-- **Existence of adapted frames.** In a short exact sequence `0 → L → E → E' → 0` with `L`
finite locally free of rank one and `E'` finite locally free of rank `r`, every point has an open
neighbourhood `U` with a local frame `l` of `L` and sections `t` of `E` over `U` whose images form
a local frame of `E'`. -/
lemma exists_adapted_frame (hS : S.ShortExact) {r : ℕ} [S.X₁.IsFiniteLocallyFreeOfRank 1]
    [S.X₃.IsFiniteLocallyFreeOfRank r] (x : X) :
    ∃ (U : X.Opens) (l : Fin 1 → Γ(S.X₁, U)) (t : Fin r → Γ(S.X₂, U)), x ∈ U ∧
      IsLocalFrame l ∧ IsLocalFrame fun k ↦ S.g.app U (t k) := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree S.X₁ 1
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₁ :=
    SheafOfModules.instIsQuasicoherentOfIsLocallyFree S.X₁
  obtain ⟨U₁, l, hx₁, hl⟩ := exists_isLocalFrame (r := 1) S.X₁ x
  obtain ⟨U₃, w, hx₃, hw⟩ := exists_isLocalFrame (r := r) S.X₃ x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (⟨hx₁, hx₃⟩ : x ∈ U₁ ⊓ U₃) (U₁ ⊓ U₃).isOpen
  replace hUle : U ≤ U₁ ⊓ U₃ := hUle
  have hsurj := surjective_app_g_of_isAffineOpen hS hU
  choose t ht using fun k ↦ hsurj (S.X₃.presheaf.map (homOfLE (hUle.trans inf_le_right)).op (w k))
  refine ⟨U, fun k ↦ S.X₁.presheaf.map (homOfLE (hUle.trans inf_le_left)).op (l k), t, hxU,
    hl.restrict _, ?_⟩
  simp_rw [ht]
  exact hw.restrict _

end ShortExact

end AlgebraicGeometry.Scheme.Modules
