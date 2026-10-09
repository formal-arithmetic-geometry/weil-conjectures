/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The projective line over a field is a smooth integral curve

## Main statements

- `AlgebraicGeometry.ProjectiveLine.smoothOfRelativeDimension_one`: `ℙ¹_S ⟶ S` is smooth of
  relative dimension one; it is covered by the two standard opens, each an affine line.
- `AlgebraicGeometry.ProjectiveLine.isIntegral`: `ℙ¹_k` is integral for a field `k`.
- `AlgebraicGeometry.ProjectiveLine.not_isClosed_homOfSections`: for `t` transcendental over
  `k`, the point `[1 : t]` of `ℙ¹_k` is not closed.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveLine

/-- The projective line `ℙ¹_S ⟶ S` is smooth of relative dimension one: on the standard open
`D₊(Tᵢ)` it is the affine line `𝔸¹_S`. -/
instance smoothOfRelativeDimension_one (S : Scheme.{u}) :
    SmoothOfRelativeDimension 1 (ProjectiveLine S ↘ S) := by
  refine smoothOfRelativeDimension_of_forall_exists_mem _ 1 fun y ↦ ?_
  have : y ∈ (⊤ : (ProjectiveLine S).Opens) := trivial
  rw [← ProjectiveSpace.iSup_standardOpen, TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  refine ⟨_, hi, ?_⟩
  rw [← ProjectiveSpace.standardOpenIso_hom_over]
  have h : Nat.card {j : ULift.{u} (Fin 2) // j ≠ i} = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_ulift]
    simp
  have := AffineSpace.smoothOfRelativeDimension_over {j : ULift.{u} (Fin 2) // j ≠ i} S
  rw [h] at this
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- The projective line over a field is connected: its two standard opens are affine lines,
and they meet. -/
instance connectedSpace (k : Type u) [Field k] :
    ConnectedSpace (ProjectiveLine (Spec (.of k))) := by
  have hs : Ideal.span (Set.range (fun _ : ULift.{u} (Fin 2) ↦
      (1 : Γ(Spec (.of k), ⊤)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨0⟩, rfl⟩) isUnit_one
  let x : ProjectiveLine (Spec (.of k)) :=
    ProjectiveSpace.homOfSections (𝟙 _) _ hs (IsLocalRing.closedPoint k)
  have hx (i) : x ∈ ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i := by
    have h : IsLocalRing.closedPoint k ∈ ProjectiveSpace.homOfSections (𝟙 _) _ hs ⁻¹ᵁ
        ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i := by
      rw [ProjectiveSpace.homOfSections_preimage_standardOpen, Scheme.basicOpen_of_isUnit _
        isUnit_one]
      trivial
    exact h
  have hconn (i) : _root_.IsConnected ((ProjectiveSpace.standardOpen (ULift.{u} (Fin 2))
      (Spec (.of k)) i : (ProjectiveLine (Spec (.of k))).Opens) :
        Set (ProjectiveLine (Spec (.of k)))) := by
    let e := ProjectiveSpace.standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) i ≪≫
      AffineSpace.SpecIso _ (.of k)
    have : (Set.range (e.inv ≫
        (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i).ι)) =
        (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) i : Set _) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        show Set.range e.inv = Set.univ from Set.range_eq_univ.mpr e.inv.homeomorph.surjective,
        Set.image_univ, Scheme.Opens.range_ι]
    rw [← this]
    exact isConnected_range (e.inv ≫ _).continuous
  refine connectedSpace_iff_univ.mpr ⟨⟨x, trivial⟩, ?_⟩
  have : (Set.univ : Set (ProjectiveLine (Spec (.of k)))) =
      (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩ : Set _) ∪
        (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨1⟩ : Set _) := by
    refine (Set.eq_univ_of_forall fun y ↦ ?_).symm
    have : y ∈ (⊤ : (ProjectiveLine (Spec (.of k))).Opens) := trivial
    rw [← ProjectiveSpace.iSup_standardOpen, TopologicalSpace.Opens.mem_iSup] at this
    obtain ⟨⟨i⟩, hi⟩ := this
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  rw [this]
  exact ((hconn _).union ⟨x, hx _, hx _⟩ (hconn _)).isPreconnected

/-- The projective line over a field is integral. -/
instance isIntegral (k : Type u) [Field k] : IsIntegral (ProjectiveLine (Spec (.of k))) := by
  have := SmoothOfRelativeDimension.smooth 1 (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have := IsRegular.of_smooth (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  exact IsRegular.isIntegral _

end AlgebraicGeometry.ProjectiveLine

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace

set_option maxHeartbeats 400000 in
/-- **A transcendental point of `ℙ¹` is not closed.** Let `K` be a field over `k` and `t ∈ K`
transcendental over `k`. The `K`-point `[1 : t]` of `ℙ¹_k` is not a closed point: in the chart
`D₊(T₀) = Spec k[T]` it is the prime `ker (T ↦ t) = 0`, which is not maximal. -/
theorem not_isClosed_homOfSections {k K : Type u} [Field k] [Field K] (φ : k →+* K) (t : K)
    (ht : letI := φ.toAlgebra; Transcendental k t)
    (hs : Ideal.span (Set.range fun i : ULift.{u} (Fin 2) ↦
      (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down)) = ⊤) (z : Spec (.of K)) :
    ¬ IsClosed {homOfSections (Spec.map (CommRingCat.ofHom φ))
      (fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down)) hs z} := by
  set s := fun i : ULift.{u} (Fin 2) ↦ (Scheme.ΓSpecIso (.of K)).inv (![1, t] i.down)
  have hs0 : s ⟨0⟩ = 1 := by simp [s]
  have hB : (Spec (.of K)).basicOpen (s ⟨0⟩) = ⊤ := by
    rw [hs0]
    exact Scheme.basicOpen_of_isUnit _ isUnit_one
  have : IsIso ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι := Scheme.Opens.isIso_ι_of_eq_top hB
  let r : Spec (.of K) ⟶ Spec (.of (MvPolynomial {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} k)) :=
    inv ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι ≫
      (homOfSections (Spec.map (CommRingCat.ofHom φ)) s hs).resLE
        (standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩) ((Spec (.of K)).basicOpen (s ⟨0⟩))
        (homOfSections_preimage_standardOpen _ s hs ⟨0⟩).ge ≫
      (standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩).hom ≫
        (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom
  have hover : r ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      Spec.map (CommRingCat.ofHom φ) := by
    have e : (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom ≫
        Spec.map (CommRingCat.ofHom MvPolynomial.C) =
        𝔸({j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}; Spec (.of k)) ↘ Spec (.of k) := by
      rw [← AffineSpace.SpecIso_inv_over, Iso.hom_inv_id_assoc]
    simp only [r, Category.assoc, e, standardOpenIso_hom_over, homOfSections_resLE_ι_over,
      IsIso.inv_hom_id_assoc]
  have hX (j : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}) :
      r.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j)) = (Scheme.ΓSpecIso _).inv t := by
    have h₁ : (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom.appTop
        ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j)) = AffineSpace.coord _ j := by
      rw [← AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
      rfl
    have h₂ := homOfSections_resLE_standardOpenIso_hom (Spec.map (CommRingCat.ofHom φ)) s hs
      ⟨0⟩
    have h₃ : (Spec (.of K)).divBasicOpen (s j.1) (s ⟨0⟩) =
        ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι.appTop ((Scheme.ΓSpecIso _).inv t) := by
      have hj : j.1 = ⟨1⟩ := by
        obtain ⟨⟨a⟩, ha⟩ := j
        have : a = 1 := by grind
        subst this; rfl
      have h1 : ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι.appTop (s ⟨0⟩) = 1 :=
        (congrArg _ hs0).trans (map_one _)
      have := Scheme.divBasicOpen_mul_self (Spec (.of K)) (s j.1) (s ⟨0⟩)
      rw [h1, mul_one] at this
      rw [this, hj]
      rfl
    have hr : r = inv ((Spec (.of K)).basicOpen (s ⟨0⟩)).ι ≫ AffineSpace.homOfVector
        (((Spec (.of K)).basicOpen (s ⟨0⟩)).ι ≫ Spec.map (CommRingCat.ofHom φ))
        (fun j ↦ (Spec (.of K)).divBasicOpen (s j.1) (s ⟨0⟩)) ≫
        (AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)).hom := by
      simp only [r, ← h₂, Category.assoc]
    rw [hr, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply, h₁, AffineSpace.homOfVector_appTop_coord, h₃,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.inv_hom_id,
      Scheme.Hom.id_appTop]
    rfl
  let ψ := MvPolynomial.eval₂Hom φ (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦ t)
  have hψ : r = Spec.map (CommRingCat.ofHom ψ) := by
    refine ext_of_isAffine ?_
    rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
    ext1
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun j ↦ ?_)
    · have h := congrArg (fun f ↦ f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) hover
      have e₁ : (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ :=
          {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}) (R := k)))).appTop
          ((Scheme.ΓSpecIso (.of k)).inv c) = (Scheme.ΓSpecIso _).inv (MvPolynomial.C c) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      have e₂ : (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of k)).inv c) =
          (Scheme.ΓSpecIso (.of K)).inv (φ c) := by
        rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
        rfl
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e₁, e₂] at h
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply, h]
      simp [ψ]
    · rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hX j]
      simp [ψ]
  have hinj : Function.Injective ψ := by
    let := φ.toAlgebra
    have : AlgebraicIndependent k (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦ t) := by
      have : Unique {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} :=
        ⟨⟨⟨⟨1⟩, by decide⟩⟩, fun ⟨⟨a⟩, ha⟩ ↦ by
          have : a = 1 := by grind
          subst this; rfl⟩
      exact algebraicIndependent_unique_type_iff.mpr ht
    exact this
  intro hz
  set g := homOfSections (Spec.map (CommRingCat.ofHom φ)) s hs
  let D := standardOpen (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩
  let B := (Spec (.of K)).basicOpen (s ⟨0⟩)
  let w : D.toScheme := g.resLE D B (homOfSections_preimage_standardOpen _ s hs ⟨0⟩).ge
    (inv B.ι z)
  have hw : D.ι w = g z := by
    simp only [w]
    rw [← Scheme.Hom.comp_apply]
    simp only [D, B, Scheme.Hom.resLE_comp_ι]
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc]
  have hwc : IsClosed ({w} : Set D.toScheme) := by
    have : ({w} : Set D.toScheme) = D.ι ⁻¹' {g z} := by
      ext a
      simp only [Set.mem_singleton_iff, Set.mem_preimage, ← hw]
      exact D.ι.isOpenEmbedding.injective.eq_iff.symm
    rw [this]
    exact hz.preimage D.ι.continuous
  let e := standardOpenIso (ULift.{u} (Fin 2)) (Spec (.of k)) ⟨0⟩ ≪≫
    AffineSpace.SpecIso {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} (.of k)
  have hrz : r z = e.hom w := rfl
  have hc : IsClosed ({r z} : Set _) := by
    rw [hrz, ← Set.image_singleton]
    exact e.hom.homeomorph.isClosedMap _ hwc
  replace hc : (r z).asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hc
  have hbot : (r z).asIdeal = ⊥ := by
    rw [hψ]
    change Ideal.comap ψ z.asIdeal = ⊥
    have : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.isPrime.ne_top
    rw [this, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot ψ).mp hinj]
  rw [hbot, ← Ring.isField_iff_maximal_bot] at hc
  have : Unique {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} :=
    ⟨⟨⟨⟨1⟩, by decide⟩⟩, fun ⟨⟨a⟩, ha⟩ ↦ by
      have : a = 1 := by grind
      subst this; rfl⟩
  exact Polynomial.not_isField k
    ((MvPolynomial.uniqueAlgEquiv (R := k) {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩}).symm.toMulEquiv.isField
      hc)

end AlgebraicGeometry.ProjectiveLine
