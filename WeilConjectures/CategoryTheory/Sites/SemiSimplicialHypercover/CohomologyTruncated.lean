/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.Cohomology

/-!
# Classes of hypercover cocycles only depend on truncations

The class in `Ext^q(R, F)` of a cocycle `z ∈ F(U_q)` on a hypercover `U` only depends on the
truncation of `U` in degrees `≤ q`: if `V` is another hypercover and `f_n : V_n ⟶ U_n` (`n ≤ q`)
are morphisms commuting with the face maps, then the restriction of `z` along `f_q` (if it is a
cocycle on `V`) has the same class as `z`
(`CategoryTheory.SemiSimplicialObject.IsHypercover.cohomologyClass_restrict_of_le`). This is the
truncated version of `CategoryTheory.SemiSimplicialObject.IsHypercover.cohomologyClass_restrict`.

It follows from the corresponding statement for classes of cocycles on resolutions
(`ChainComplex.IsResolution.cocycleClass_naturality_of_le`): the class of a `q`-cocycle only
involves the splicing of the resolution in degrees `< q`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Abelian

namespace CategoryTheory.Abelian.Splicing

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜] (P : Splicing 𝒜)

/-- Naturality of `Splicing.extClass` in degree `n` with respect to morphisms of splicings
which are only given in degrees `≤ n`. -/
lemma extClass_comp_mk₀_of_le (Q : Splicing 𝒜) (n : ℕ) (a : ∀ m, m ≤ n → (P.X m ⟶ Q.X m))
    (b : ∀ m, m < n → (P.Y m ⟶ Q.Y m))
    (ha : ∀ m (h : m < n), P.f m ≫ b m h = a (m + 1) h ≫ Q.f m)
    (hb : ∀ m (h : m < n), P.g m ≫ a m h.le = b m h ≫ Q.g m) :
    (P.extClass n).comp (Ext.mk₀ (a n le_rfl)) (add_zero n) =
      (Ext.mk₀ (a 0 (Nat.zero_le n))).comp (Q.extClass n) (zero_add n) := by
  induction n with
  | zero => simp [Ext.mk₀_comp_mk₀]
  | succ n ih =>
    rw [extClass_succ, extClass_succ, Ext.comp_assoc_of_third_deg_zero,
      (P.shortExact n).extClass_naturality (Q.shortExact n)
        { τ₁ := a (n + 1) le_rfl, τ₂ := b n (Nat.lt_succ_self n), τ₃ := a n (Nat.le_succ n),
          comm₁₂ := (ha n _).symm, comm₂₃ := (hb n _).symm },
      ← Ext.comp_assoc_of_second_deg_zero,
      ih (fun m h ↦ a m (h.trans (Nat.le_succ n))) (fun m h ↦ b m (h.trans (Nat.lt_succ_self n)))
        (fun m h ↦ ha m (h.trans (Nat.lt_succ_self n)))
        (fun m h ↦ hb m (h.trans (Nat.lt_succ_self n)))]
    exact Ext.comp_assoc _ _ _ _ _ (by lia)

end CategoryTheory.Abelian.Splicing

namespace ChainComplex.IsResolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {K : ChainComplex 𝒜 ℕ} {A : 𝒜}
  {ε : K.X 0 ⟶ A}

/-- Comparison maps, in degrees `≤ q`, from a splicing `P` mapping to `K` in degrees `≤ q` into
the canonical splicing of `K`. -/
noncomputable def compMapOfLE (hK : IsResolution K ε) (P : Splicing 𝒜) (q : ℕ)
    (τ : ∀ n, n ≤ q → (P.Y n ⟶ K.X n)) (a₀ : P.X 0 ⟶ A)
    (h₀ : P.g 0 ≫ a₀ = τ 0 (Nat.zero_le q) ≫ ε)
    (hτ : ∀ n (h : n < q), τ (n + 1) h ≫ K.d (n + 1) n = P.g (n + 1) ≫ P.f n ≫ τ n h.le) :
    (n : ℕ) → (h : n ≤ q) → {a : P.X n ⟶ hK.B n // P.g n ≫ a = τ n h ≫ hK.π n}
  | 0, _ => ⟨a₀, h₀⟩
  | n + 1, h => ⟨hK.liftB n (P.f n ≫ τ n (by omega)) (by
      rw [Category.assoc, ← π_j, ← Category.assoc (τ n _),
        ← (hK.compMapOfLE P q τ a₀ h₀ hτ n (by omega)).2, Category.assoc, P.w_assoc,
        zero_comp]), by
      rw [← cancel_mono (hK.ι n), Category.assoc, Category.assoc, π_ι, hτ n h, liftB_ι]⟩

variable [HasExt.{w} 𝒜] (hK : IsResolution K ε)
include hK

/-- Comparison of a splicing `P` mapping to `K` in degrees `≤ q` with the canonical splicing of
`K`, in degree `q`. -/
lemma splicing_extClass_comp_mk₀_of_le (P : Splicing 𝒜) (q : ℕ)
    (τ : ∀ n, n ≤ q → (P.Y n ⟶ K.X n)) (a₀ : P.X 0 ⟶ A)
    (h₀ : P.g 0 ≫ a₀ = τ 0 (Nat.zero_le q) ≫ ε)
    (hτ : ∀ n (h : n < q), τ (n + 1) h ≫ K.d (n + 1) n = P.g (n + 1) ≫ P.f n ≫ τ n h.le)
    {F : 𝒜} (φ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0) (φ' : P.X q ⟶ F)
    (hφ' : P.g q ≫ φ' = τ q le_rfl ≫ φ) :
    (P.extClass q).comp (Ext.mk₀ φ') (add_zero q) =
      (Ext.mk₀ a₀).comp (hK.cocycleClass q φ hφ) (zero_add q) := by
  obtain rfl : φ' = (hK.compMapOfLE P q τ a₀ h₀ hτ q le_rfl).1 ≫ hK.desc q φ hφ := by
    rw [← cancel_epi (P.g q), hφ', ← Category.assoc,
      (hK.compMapOfLE P q τ a₀ h₀ hτ q le_rfl).2, Category.assoc, π_desc]
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    P.extClass_comp_mk₀_of_le hK.splicing q (fun n h ↦ (hK.compMapOfLE P q τ a₀ h₀ hτ n h).1)
      (fun n h ↦ τ n h.le) (fun n h ↦ (hK.liftB_ι _ _ _).symm)
      (fun n h ↦ (hK.compMapOfLE P q τ a₀ h₀ hτ n h.le).2)]
  exact Ext.comp_assoc _ _ _ _ _ (by lia)

/-- **Naturality of classes of cocycles for truncated morphisms of resolutions**: the class of a
`q`-cocycle is compatible with maps of resolutions of `A` which are only given (and commute with
the differentials) in degrees `≤ q`. -/
lemma cocycleClass_naturality_of_le {K' : ChainComplex 𝒜 ℕ} {ε' : K'.X 0 ⟶ A}
    (hK' : IsResolution K' ε') (q : ℕ) (τ : ∀ n, n ≤ q → (K'.X n ⟶ K.X n))
    (h₀ : τ 0 (Nat.zero_le q) ≫ ε = ε')
    (hτ : ∀ n (h : n < q), τ (n + 1) h ≫ K.d (n + 1) n = K'.d (n + 1) n ≫ τ n h.le)
    {F : 𝒜} (φ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0)
    (hφ' : K'.d (q + 1) q ≫ τ q le_rfl ≫ φ = 0) :
    hK'.cocycleClass q (τ q le_rfl ≫ φ) hφ' = hK.cocycleClass q φ hφ := by
  rw [← Ext.mk₀_id_comp (hK.cocycleClass q φ hφ)]
  exact hK.splicing_extClass_comp_mk₀_of_le hK'.splicing q τ (𝟙 A)
    ((Category.comp_id _).trans h₀.symm) (fun n h ↦ by simp [hτ n h]) φ hφ _ (by simp)

end ChainComplex.IsResolution

namespace CategoryTheory.SemiSimplicialObject.IsHypercover

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Type (max u v)} [Ring R] [HasSheafify J (ModuleCat.{max u v} R)]
  [HasExt.{w} (Sheaf J (ModuleCat.{max u v} R))] {U V : SemiSimplicialObject C}

/-- **Classes of cocycles only depend on truncations**: if `f_n : V_n ⟶ U_n` (`n ≤ q`) are
morphisms between hypercovers commuting with the face maps, the class of the restriction along
`f_q` of a `q`-cocycle `z` on `U` is the class of `z`. -/
lemma cohomologyClass_restrict_of_le (hU : U.IsHypercover J) (hV : V.IsHypercover J) (q : ℕ)
    (f : ∀ n, n ≤ q → (V.obj n ⟶ U.obj n))
    (hf : ∀ n (h : n < q) (i : Fin (n + 2)), f (n + 1) h ≫ U.δ n i = V.δ n i ≫ f n h.le)
    (F : Sheaf J (ModuleCat.{max u v} R)) (z : F.obj.obj (Opposite.op (U.obj q)))
    (hz : U.IsCocycle F q z) (hz' : V.IsCocycle F q ((F.obj.map (f q le_rfl).op).hom z)) :
    hV.cohomologyClass F q ((F.obj.map (f q le_rfl).op).hom z) hz' =
      hU.cohomologyClass F q z hz := by
  have key : (freeSheafHomEquiv J R (V.obj q) F).symm ((F.obj.map (f q le_rfl).op).hom z) =
      (freeSheaf J R).map (f q le_rfl) ≫ (freeSheafHomEquiv J R (U.obj q) F).symm z := by
    apply (freeSheafHomEquiv J R (V.obj q) F).injective
    rw [Equiv.apply_symm_apply, freeSheafHomEquiv_map_comp, Equiv.apply_symm_apply]
  rw [cohomologyClass, cohomologyClass, hV.isResolution.cocycleClass_congr q key _
    (key ▸ (isCocycle_iff_d_comp_eq_zero _).1 hz')]
  refine hU.isResolution.cocycleClass_naturality_of_le hV.isResolution q
    (fun n h ↦ (freeSheaf J R).map (f n h)) ?_ (fun n h ↦ ?_) _ _ _
  · rw [freeAugmentation, freeAugmentation,
      ← freeYoneda_map_comp_freeYonedaToConst (f 0 (Nat.zero_le q)), Functor.map_comp]
    rfl
  · rw [freeComplex_d, freeComplex_d, Preadditive.sum_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, ← Functor.map_comp, ← Functor.map_comp,
      hf n h i]

end CategoryTheory.SemiSimplicialObject.IsHypercover
