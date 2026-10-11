/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechExact
public import WeilConjectures.AlgebraicGeometry.Modules.InvertibleFibre
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Picard.Representability
public import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer

/-!
# Sections of `F`-classes do not vanish on fibres

Let `f : X ⟶ Spec k` be flat, proper and of finite presentation, and let `ℒ ∈ Pic(X_T)` satisfy
`AlgebraicGeometry.IsInvertibleDirectImage`, i.e. `R f_{T,*} ℒ` is an invertible module placed in
degree `0`. If `s` is a free generator of `f_{T,*} ℒ` over an affine open `V ⊆ T`, then the
pullback of `s` to the fibre `X_t` over every point `t ∈ V` is nonzero
(`AlgebraicGeometry.pullbackSection_baseChangeMap_ne_zero`).

This is the degree `0` part of cohomology and base change. Over `A = Γ(T, V)`, the sections of
`ℒ` over `f_T⁻¹ V` are the kernel of the first differential of the Čech complex `Č` of a
finite affine cover trivializing `ℒ`, whose terms are flat over `A`. For every `A`-algebra `B`
the base change `B ⊗[A] Č` is the Čech complex of the pullback of `ℒ` to `X_B`
(`AlgebraicGeometry.Scheme.Modules.cechBaseChange_bijective`), which is exact in degree `1`
since `ℒ_B` still satisfies the condition. Taking `B = A ⊕ M` a square-zero extension, `M ⊗[A] Č`
is exact in degree `1` for every `A`-module `M`; hence `Γ(f_T⁻¹ V, ℒ) ⊗[A] B ⟶ B ⊗[A] Č⁰` is
injective (`Module.Flat.lTensor_injective_ker_subtype`), and for `B = κ(t)` this sends
`s ⊗ 1 ≠ 0` to the family of pullbacks of `s`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite TopCat.Presheaf

namespace AlgebraicGeometry

open Scheme Modules

/-- **Finite trivializing affine covers.** A quasi-compact open `W` of a scheme is covered by
finitely many affine opens contained in `W` on which a given invertible module has free
generators. -/
lemma Scheme.Modules.exists_finite_cover_isFreeGenerator {Y : Scheme.{u}} (ℒ : Y.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} ℒ] {W : Y.Opens} (hW : IsCompact (W : Set Y)) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → Y.Opens), (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, U i ≤ W) ∧ ⨆ i, U i = W ∧ ∀ i, ∃ e : Γ(ℒ, U i), IsFreeGenerator e := by
  choose U hxU hUW he using fun x : W ↦ exists_isFreeGenerator ℒ x.2
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover (fun x : W ↦ ((U x).1 : Set Y))
    (fun x ↦ (U x).1.isOpen) (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU _⟩)
  refine ⟨s, inferInstance, fun x ↦ (U x).1, fun x ↦ (U x).2, fun x ↦ hUW x, ?_,
    fun x ↦ he x⟩
  refine le_antisymm (iSup_le fun x ↦ hUW x) fun x hx ↦ ?_
  obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hys⟩, hxy⟩

/-- Finite intersections of affine opens lying over an affine open of the target of a
separated morphism are affine. -/
lemma isAffineOpen_iInf_of_isSeparated {Y T : Scheme.{u}} (p : Y ⟶ T) [IsSeparated p]
    {V : T.Opens} (hV : IsAffineOpen V) {ι : Type u} (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hUV : ∀ i, U i ≤ p ⁻¹ᵁ V) {k : ℕ} (y : Fin (k + 1) → ι) :
    IsAffineOpen (⨅ l, U (y l)) := by
  have H := isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal p)) V hV
  have key : ∀ (s : Finset (Fin (k + 1))), s.Nonempty →
      IsAffineOpen (⨅ l ∈ s, U (y l)) ∧ ⨅ l ∈ s, U (y l) ≤ p ⁻¹ᵁ V := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a => simpa using ⟨hU (y a), hUV (y a)⟩
    | cons a s ha hs ih =>
      rw [Finset.cons_eq_insert, Finset.iInf_insert]
      exact ⟨H _ (hUV _) _ ih.2 (hU _) ih.1, inf_le_left.trans (hUV _)⟩
  simpa using (key Finset.univ Finset.univ_nonempty).1


section Core

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Flat f] [IsProper f]
  [LocallyOfFinitePresentation f]
  [∀ T : Over (Spec (.of k)), HasInjectiveResolutions (Limits.pullback f T.hom).Modules]

/-- **Pullbacks of generators of `f_{T,*} ℒ` to fibres are nonzero.** Let `ℒ ∈ Pic(X_T)` satisfy
`IsInvertibleDirectImage`, let `s` be a free generator of `f_{T,*} ℒ` on an affine open `V ⊆ T`
and let `i : T' ⟶ T` be a morphism from an affine scheme with nonzero ring of functions, landing
in `V`. Then the pullback of `s` to `X_{T'}` is nonzero.

This is the degree `0` part of cohomology and base change: see the module documentation. -/
theorem pullbackSection_baseChangeMap_ne_zero {T : Over (Spec (.of k))}
    {L : (Limits.pullback f T.hom).Pic} (hL : IsInvertibleDirectImage f T L)
    {V : T.left.Opens} (hV : IsAffineOpen V)
    {s : Γ((pushforward (Limits.pullback.snd f T.hom)).obj ((fromSkeleton _).obj L.val), V)}
    (hs : IsFreeGenerator s) {T' : Over (Spec (.of k))} (i : T' ⟶ T) [IsAffine T'.left]
    [Nontrivial Γ(T'.left, ⊤)] (hi : ⊤ ≤ i.left ⁻¹ᵁ V) :
    pullbackSection (baseChangeMap f i)
      (show Γ((fromSkeleton _).obj L.val, Limits.pullback.snd f T.hom ⁻¹ᵁ V) from s) ≠ 0 := by
  classical
  set sT := Limits.pullback.snd f T.hom with hsT
  set ℒ := (fromSkeleton _).obj L.val with hℒ
  have : SheafOfModules.IsInvertible.{u, u, u} ℒ := L.isInvertible
  have : ℒ.IsInvertible := IsInvertible.of_sheafOfModules _
  have hW := sT.isCompact_preimage hV.isCompact
  obtain ⟨ι, _, U, hUa, hUV, hUsup, he⟩ := exists_finite_cover_isFreeGenerator ℒ hW
  have := Fintype.ofFinite ι
  let instC : ∀ (k : ℕ) (y : Fin (k + 1) → ι), Module Γ(T.left, V) Γ(ℒ, ⨅ l, U (y l)) :=
    fun k y ↦ Module.compHom _ (sT.appLE V _ (iInf_le_preimage_of_forall_le U hUV y)).hom
  have hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι) (a : Γ(T.left, V)) (x : Γ(ℒ, ⨅ l, U (y l))),
      a • x = sT.appLE V _ (iInf_le_preimage_of_forall_le U hUV y) a • x :=
    fun _ _ _ _ ↦ rfl
  have hUa' (k : ℕ) (y : Fin (k + 1) → ι) : IsAffineOpen (⨅ l, U (y l)) :=
    isAffineOpen_iInf_of_isSeparated sT hV U hUa hUV y
  have he' (k : ℕ) (y : Fin (k + 1) → ι) : ∃ e : Γ(ℒ, ⨅ l, U (y l)), IsFreeGenerator e := by
    obtain ⟨e, he⟩ := he (y 0)
    exact ⟨_, he.map (iInf_le _ 0)⟩
  -- the Čech complex stays exact in degree `1` after base change to affine `T''` over `V`
  have hexB : ∀ (T'' : Over (Spec (.of k))) (j : T'' ⟶ T) [IsAffine T''.left]
      (hj : ⊤ ≤ j.left ⁻¹ᵁ V),
      letI := (j.left.appLE V ⊤ hj).hom.toAlgebra
      Function.Exact ((cechDifferential ℒ U hUV hU 0).lTensor Γ(T''.left, ⊤))
        ((cechDifferential ℒ U hUV hU 1).lTensor Γ(T''.left, ⊤)) := by
    intro T'' j _ hj
    let := (j.left.appLE V ⊤ hj).hom.toAlgebra
    have H := isPullback_baseChangeMap f j
    have hL'' := IsInvertibleDirectImage.map_of_isProper f j hL
    have : ((Modules.pullback (baseChangeMap f j)).obj ℒ).IsInvertible :=
      IsInvertible.pullback ..
    have hZ : IsZero ((higherDirectImage (Limits.pullback.snd f T''.hom) 1).obj
        ((Modules.pullback (baseChangeMap f j)).obj ℒ)) :=
      (hL''.2 1 one_pos).of_iso ((higherDirectImage _ 1).mapIso (fromSkeletonToSkeletonIso _).symm)
    have hsup : ⨆ i, baseChangeMap f j ⁻¹ᵁ U i = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, hUsup, ← Scheme.Hom.comp_preimage, H.w,
        Scheme.Hom.comp_preimage, eq_top_iff]
      exact (Scheme.Hom.preimage_top _).ge.trans (Scheme.Hom.preimage_mono _ hj)
    exact exact_lTensor_cechDifferential hj ℒ U hUV rfl hU H hV hUa' he'
      (exactAt_cechComplex_of_isZero_higherDirectImage (Limits.pullback.snd f T''.hom) _
        (fun i ↦ isAffineOpen_preimage_of_isPullback H hV hj (hUV i) (hUa i)) hsup _ 1 hZ)
  sorry

end Core

end AlgebraicGeometry
