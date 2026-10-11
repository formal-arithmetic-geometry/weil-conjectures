/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.Specialization
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite refinements of étale morphisms: the induction on the fibre degree

Let `u : U ⟶ X` be étale, separated, quasi-compact and surjective, with `X` quasi-compact and
quasi-separated. We show that finitely many finite morphisms `rₖ : Tₖ ⟶ X`, jointly surjective,
factor through `u` Zariski locally on their sources (`Scheme.Hom.HasFiniteRefinement`).

The proof is the induction of Stacks 09Z0 on a bound `d` for the geometric fibres of `u`. By
Zariski's main theorem `u` is an open immersion `j : U ⟶ Y` followed by a finite `p : Y ⟶ X`,
and replacing `Y` by the scheme-theoretic image of `j` we may assume `U` dense in `Y`. Then
`U ×_X Y = U ⊔ W`, where the first summand is the graph of `j`, and the image `V ⊆ Y` of the
étale `W ⟶ Y` contains `Y ∖ U`. The geometric fibres of `W ⟶ V` are bounded by `d - 1`: over
`U` the graph has been removed, and over `Y ∖ U` the fibre of `u` is smaller by density
(`Scheme.Hom.card_lifts_le_of_specializes`). By induction `W ⟶ V` has a finite refinement; we
extend it to finite `Y`-schemes by Zariski's main theorem and add the reduced complement
`Y ∖ V ⊆ U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

variable {T U X : Scheme.{u}}

/-- `r : T ⟶ X` **factors through `u : U ⟶ X` Zariski locally on `T`**: every point of `T` has
an open neighbourhood `O` with an `X`-morphism `O ⟶ U`. -/
def Scheme.Hom.LocallyFactorsThrough (r : T ⟶ X) (u : U ⟶ X) : Prop :=
  ∀ t : T, ∃ (O : T.Opens) (_ : t ∈ O) (φ : O.toScheme ⟶ U), φ ≫ u = O.ι ≫ r

/-- `u : U ⟶ X` **has a finite refinement**: finitely many finite morphisms `rₖ : Tₖ ⟶ X`,
jointly surjective, factor through `u` Zariski locally on their sources. -/
def Scheme.Hom.HasFiniteRefinement (u : U ⟶ X) : Prop :=
  ∃ (K : Type) (_ : Finite K) (T : K → Scheme.{u}) (r : ∀ k, T k ⟶ X), (∀ k, IsFinite (r k)) ∧
    (∀ x : X, ∃ k t, r k t = x) ∧ ∀ k, (r k).LocallyFactorsThrough u

/-- A surjective morphism whose geometric fibres are empty has empty target. -/
lemma Scheme.Hom.isEmpty_of_hasGeometricFibersCardLE_zero (u : U ⟶ X) [Surjective u]
    (hd : u.HasGeometricFibersCardLE 0) : IsEmpty X := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨x', rfl⟩ := u.surjective x
  have h := hd _ (U.sepClosurePoint x' ≫ u)
  rw [Nat.cast_zero, nonpos_iff_eq_zero, ENat.card_eq_zero_iff_empty] at h
  exact h.false ⟨_, rfl⟩

/-- **Extending a finite morphism over an open.** A finite `z : Z ⟶ V` to a quasi-compact open
`V` of a quasi-compact quasi-separated scheme `Y` is the part over `V` of a finite `Y`-scheme
`Z'`: by
Zariski's main theorem `Z` is open in a finite `Y`-scheme, and we take the scheme-theoretic image
of `Z`, in which `Z` is closed over `V` since `z` is universally closed. -/
lemma Scheme.Hom.exists_isFinite_extension {Y Z : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (V : Y.Opens) [CompactSpace V] (z : Z ⟶ V) [IsFinite z] :
    ∃ (Z' : Scheme.{u}) (e : Z ⟶ Z') (pz : Z' ⟶ Y), IsOpenImmersion e ∧ IsFinite pz ∧
      e ≫ pz = z ≫ V.ι ∧ ∀ ζ, pz ζ ∈ V → ζ ∈ Set.range e.base := by
  obtain ⟨Z₀, e₀, p₀, _, _, _, he₀⟩ :=
    (z ≫ V.ι).exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  have hepz : e₀.toImage ≫ e₀.imageι ≫ p₀ = z ≫ V.ι := by simp [he₀]
  refine ⟨e₀.image, e₀.toImage, e₀.imageι ≫ p₀, inferInstance, inferInstance, hepz, ?_⟩
  intro ζ hζ
  set pz := e₀.imageι ≫ p₀
  set e := e₀.toImage
  let O := pz ⁻¹ᵁ V
  have heO : Set.range e.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    change pz (e t) ∈ V
    rw [← Scheme.Hom.comp_apply, hepz, Scheme.Hom.comp_apply]
    exact (z t).2
  let e' := IsOpenImmersion.lift O.ι e heO
  have he' : e' ≫ pz ∣_ V = z := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc,
      hepz]
  have : UniversallyClosed (e' ≫ pz ∣_ V) := by rw [he']; infer_instance
  have : UniversallyClosed e' := UniversallyClosed.of_comp_of_isSeparated e' (pz ∣_ V)
  have hcl : IsClosed (Set.range e'.base) := e'.isClosedMap.isClosed_range
  have hζ' : (⟨ζ, hζ⟩ : O) ∈ closure (Set.range e'.base) := by
    rw [O.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.mem_preimage,
      ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, IsOpenImmersion.lift_fac,
      e₀.toImage.denseRange.closure_eq]
    trivial
  obtain ⟨t, ht⟩ := hcl.closure_subset hζ'
  refine ⟨t, ?_⟩
  rw [← IsOpenImmersion.lift_fac O.ι e heO, Scheme.Hom.comp_apply]
  exact congrArg O.ι.base ht

/-- **The induction step of Stacks 09Z0.** If every étale, separated, quasi-compact surjection
onto a quasi-compact quasi-separated scheme with geometric fibres bounded by `d` has a finite
refinement, so does every such morphism with geometric fibres bounded by `d + 1`. -/
theorem Scheme.Hom.hasFiniteRefinement_of_hasGeometricFibersCardLE_succ {d : ℕ}
    (IH : ∀ {U X : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u]
      [Surjective u] [CompactSpace X] [QuasiSeparatedSpace X], u.HasGeometricFibersCardLE d →
        u.HasFiniteRefinement)
    (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u] [Surjective u] [CompactSpace X]
    [QuasiSeparatedSpace X] (hd : u.HasGeometricFibersCardLE (d + 1)) :
    u.HasFiniteRefinement := by
  -- Zariski's main theorem, and density of `U` in the scheme-theoretic image
  obtain ⟨Y₀, j₀, p₀, _, _, _, hjp₀⟩ := u.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  obtain ⟨Y, j, p, _, _, rfl, hdense⟩ : ∃ (Y : Scheme.{u}) (j : U ⟶ Y) (p : Y ⟶ X),
      IsOpenImmersion j ∧ IsFinite p ∧ j ≫ p = u ∧ DenseRange j.base :=
    ⟨_, j₀.toImage, j₀.imageι ≫ p₀, inferInstance, inferInstance, by simp [hjp₀],
      j₀.toImage.denseRange⟩
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  -- the decomposition `U ×_X Y = U ⊔ W`
  let q := pullback.snd (j ≫ p) p
  let Γ : U ⟶ pullback (j ≫ p) p := pullback.lift (𝟙 U) j (Category.id_comp _)
  have hΓq : Γ ≫ q = j := pullback.lift_snd _ _ _
  have : IsOpenImmersion Γ := by
    have : Γ = pullback.diagonal (j ≫ p) ≫ pullback.map (j ≫ p) (j ≫ p) (j ≫ p) p (𝟙 U) j (𝟙 X)
        (by simp) (by simp) := by
      apply pullback.hom_ext <;> simp [Γ]
    rw [this]
    infer_instance
  let W : (pullback (j ≫ p) p).Opens :=
    ⟨(Set.range Γ.base)ᶜ, Γ.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hW : (SetLike.coe W) = (Set.range Γ.base)ᶜ := rfl
  let V : Y.Opens := ⟨q.base '' W, q.isOpenMap (SetLike.coe W) W.2⟩
  have hWV : Set.range (W.ι ≫ q).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    rfl
  let w : W.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι (W.ι ≫ q) hWV
  have hw : w ≫ V.ι = W.ι ≫ q := IsOpenImmersion.lift_fac _ _ _
  -- `V` contains the complement of `U`
  have hVc : ∀ y, y ∉ Set.range j.base → y ∈ V := by
    intro y hy
    obtain ⟨x, hx⟩ := (j ≫ p).surjective (p y)
    obtain ⟨ζ, -, hζ₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hx
    refine ⟨ζ, ?_, hζ₂⟩
    rintro ⟨x', rfl⟩
    exact hy ⟨x', by rw [← hζ₂, ← Scheme.Hom.comp_apply, hΓq]⟩
  -- properties of `w : W ⟶ V`
  have : Etale w := by
    have : Etale (w ≫ V.ι) := by rw [hw]; infer_instance
    exact Etale.of_comp w V.ι
  have : IsSeparated w := by
    have : IsSeparated (w ≫ V.ι) := by rw [hw]; infer_instance
    exact IsSeparated.of_comp w V.ι
  have : CompactSpace ↥(pullback (j ≫ p) p) := QuasiCompact.compactSpace_of_compactSpace q
  have : CompactSpace W := isCompact_iff_compactSpace.1
    (isClosed_compl_iff.2 Γ.isOpenEmbedding.isOpen_range).isCompact
  have : CompactSpace V := isCompact_iff_compactSpace.1 ((isCompact_iff_compactSpace.2
    ‹CompactSpace W›).image q.continuous)
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated V.ι
  have : QuasiCompact w := inferInstance
  have : Surjective w := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨ζ, hζ, hζy⟩ := y.2
    refine ⟨⟨ζ, hζ⟩, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hw]
    exact hζy
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (j ≫ p)
  have : QuasiCompact j := inferInstance
  -- the geometric fibres of `w` are bounded by `d`
  have hdw : w.HasGeometricFibersCardLE d := by
    intro Ω _ _ g
    obtain ⟨a⟩ : Nonempty (Spec (.of Ω)) := inferInstance
    have e₁ : ENat.card {s // s ≫ w = g} = ENat.card {s // s ≫ W.ι ≫ q = g ≫ V.ι} :=
      ENat.card_congr ((Scheme.Hom.liftsCompMonoEquiv w V.ι g).trans
        (Equiv.subtypeEquivRight fun s ↦ by rw [hw]))
    have e₂ := ENat.card_congr (Scheme.Hom.liftsSumEquiv q Γ W hW (g ≫ V.ι))
    rw [ENat.card_sum] at e₂
    have e₃ := ENat.card_congr (Scheme.Hom.liftsPullbackSndEquiv (j ≫ p) p (g ≫ V.ι))
    have hu := hd Ω ((g ≫ V.ι) ≫ p)
    rw [e₁]
    by_cases hy : (g ≫ V.ι) a ∈ Set.range j.base
    · have hΓ : 1 ≤ ENat.card {s // s ≫ Γ ≫ q = g ≫ V.ι} := by
        rw [ENat.one_le_card_iff_nonempty]
        have hr : Set.range (g ≫ V.ι).base ⊆ Set.range j.base := by
          rintro _ ⟨b, rfl⟩
          rwa [Subsingleton.elim b a]
        exact ⟨⟨IsOpenImmersion.lift j (g ≫ V.ι) hr, by rw [hΓq, IsOpenImmersion.lift_fac]⟩⟩
      have h₅ : ENat.card {s // s ≫ W.ι ≫ q = g ≫ V.ι} + 1 ≤ (d : ℕ∞) + 1 := by
        calc _ ≤ ENat.card {s // s ≫ W.ι ≫ q = g ≫ V.ι} +
              ENat.card {s // s ≫ Γ ≫ q = g ≫ V.ι} := add_le_add_right hΓ _
          _ = _ := e₂
          _ = _ := e₃
          _ ≤ _ := by exact_mod_cast hu
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h₅
    · obtain ⟨x, hx⟩ := exists_specializes_of_mem_closure_range j
        (hdense.closure_eq ▸ Set.mem_univ ((g ≫ V.ι) a))
      have hle := (j ≫ p).card_lifts_le_of_specializes j p rfl hx ⟨x, rfl⟩ hy hd
      rw [← Scheme.Hom.comp_apply, ← (j ≫ p).card_lifts_eq_card_lifts_sepClosurePoint] at hle
      calc _ ≤ ENat.card {s // s ≫ W.ι ≫ q = g ≫ V.ι} +
            ENat.card {s // s ≫ Γ ≫ q = g ≫ V.ι} := le_self_add
        _ = _ := e₂
        _ = _ := e₃
        _ ≤ _ := hle
  obtain ⟨K, _, Z, z, _, hzsurj, hzloc⟩ := IH w hdw
  choose Z' e pz _ _ hepz hZ' using fun k ↦ Scheme.Hom.exists_isFinite_extension V (z k)
  -- the reduced complement of `V`, which lies in `U`
  let I : Y.IdealSheafData := .vanishingIdeal ⟨(V : Set Y)ᶜ, V.2.isClosed_compl⟩
  have hI : Set.range I.subschemeι.base ⊆ Set.range j.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    intro y hy
    by_contra h
    exact hy (hVc y h)
  let T' : Option K → Scheme.{u} := fun k ↦ Option.elim k I.subscheme Z'
  let r : ∀ k, T' k ⟶ X := fun k ↦ match k with
    | none => I.subschemeι ≫ p
    | some k => pz k ≫ p
  refine ⟨Option K, inferInstance, T', r, ?_, ?_, ?_⟩
  · rintro (_ | k) <;> dsimp only [r, T'] <;> infer_instance
  · intro x
    obtain ⟨x', rfl⟩ := (j ≫ p).surjective x
    by_cases hx : j x' ∈ V
    · obtain ⟨k, t, ht⟩ := hzsurj ⟨j x', hx⟩
      refine ⟨some k, e k t, ?_⟩
      change (pz k ≫ p) (e k t) = _
      rw [← Scheme.Hom.comp_apply, ← Category.assoc, hepz, Category.assoc,
        Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply]
      rfl
    · have : j x' ∈ Set.range I.subschemeι.base := by
        rw [Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hx
      obtain ⟨t, ht⟩ := this
      exact ⟨none, t, by change (I.subschemeι ≫ p) t = _; rw [Scheme.Hom.comp_apply, ht]; rfl⟩
  · rintro (_ | k) t
    · refine ⟨⊤, trivial, (⊤ : I.subscheme.Opens).ι ≫ IsOpenImmersion.lift j I.subschemeι hI, ?_⟩
      change _ = _ ≫ I.subschemeι ≫ p
      rw [Category.assoc, IsOpenImmersion.lift_fac_assoc]
    · by_cases ht : pz k t ∈ Set.range j.base
      · let O := pz k ⁻¹ᵁ j.opensRange
        have hO : Set.range (O.ι ≫ pz k).base ⊆ Set.range j.base := by
          rintro _ ⟨s, rfl⟩
          exact s.2
        refine ⟨O, ht, IsOpenImmersion.lift j (O.ι ≫ pz k) hO, ?_⟩
        change _ = _ ≫ pz k ≫ p
        rw [IsOpenImmersion.lift_fac_assoc, Category.assoc]
      · obtain ⟨t', rfl⟩ := hZ' k t (hVc _ ht)
        obtain ⟨O, hO, φ, hφ⟩ := hzloc k t'
        refine ⟨e k ''ᵁ O, ⟨t', hO, rfl⟩,
          ((e k).isoImage O).inv ≫ φ ≫ W.ι ≫ pullback.fst (j ≫ p) p, ?_⟩
        change _ = _ ≫ pz k ≫ p
        rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition,
          ← Category.assoc W.ι, ← hw, Category.assoc, reassoc_of% hφ, Iso.inv_comp_eq,
          ← Category.assoc ((e k).isoImage O).hom, Scheme.Hom.isoImage_hom_ι, Category.assoc,
          reassoc_of% hepz]

/-- **Finite refinements by induction on the fibre degree** (the integral form of Stacks 09Z0).
An étale, separated, quasi-compact surjection onto a quasi-compact quasi-separated scheme whose
geometric fibres have at most `d` points has a finite refinement. -/
theorem Scheme.Hom.hasFiniteRefinement_of_hasGeometricFibersCardLE (d : ℕ) :
    ∀ {U X : Scheme.{u}} (u : U ⟶ X) [Etale u] [IsSeparated u] [QuasiCompact u] [Surjective u]
      [CompactSpace X] [QuasiSeparatedSpace X], u.HasGeometricFibersCardLE d →
        u.HasFiniteRefinement := by
  induction d with
  | zero =>
    intro U X u _ _ _ _ _ _ hd
    have := u.isEmpty_of_hasGeometricFibersCardLE_zero hd
    exact ⟨Empty, inferInstance, Empty.elim, fun k ↦ k.elim, fun k ↦ k.elim,
      fun x ↦ isEmptyElim x, fun k ↦ k.elim⟩
  | succ d ih =>
    intro U X u _ _ _ _ _ _ hd
    exact hasFiniteRefinement_of_hasGeometricFibersCardLE_succ ih u hd

end AlgebraicGeometry
