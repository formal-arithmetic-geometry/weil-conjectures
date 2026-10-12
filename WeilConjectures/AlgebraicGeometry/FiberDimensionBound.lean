/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension

/-!
# A uniform bound on the dimension of the fibres of a morphism of finite type

Let `g : Z ⟶ Y` be locally of finite type with `Z` quasi-compact. Then the fibres of `g` over
field-valued points have uniformly bounded dimension: there is `e : ℕ` such that
`dim (Z ×_Y Spec K) ≤ e` for every field `K` and every `Spec K ⟶ Y`
(`AlgebraicGeometry.exists_topologicalKrullDim_pullback_le`).

Locally `g` is `Spec B ⟶ Spec A` with `B` a quotient of `A[x₁, …, xₙ]`, and the fibre over
`Spec K` is `Spec (B ⊗[A] K)`, a quotient of `K[x₁, …, xₙ]`, of dimension at most `n`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

/-- If `B` is a quotient of `A[x₁, …, xₙ]`, then `B ⊗[A] K` has dimension at most `n` for every
field `K` over `A`. -/
theorem ringKrullDim_tensorProduct_le_of_surjective {A B K : Type*} [CommRing A] [CommRing B]
    [Field K] [Algebra A B] [Algebra A K] (n : ℕ) (f : MvPolynomial (Fin n) A →ₐ[A] B)
    (hf : Function.Surjective f) : ringKrullDim (B ⊗[A] K) ≤ n := by
  let F := Algebra.TensorProduct.map f (AlgHom.id A K)
  have hF : Function.Surjective F := LinearMap.rTensor_surjective K (g := f.toLinearMap) hf
  let e : MvPolynomial (Fin n) A ⊗[A] K ≃ₐ[A] MvPolynomial (Fin n) K :=
    (Algebra.TensorProduct.comm A _ K).trans
      ((MvPolynomial.algebraTensorAlgEquiv A K).restrictScalars A)
  calc ringKrullDim (B ⊗[A] K)
      _ ≤ ringKrullDim (MvPolynomial (Fin n) A ⊗[A] K) :=
        ringKrullDim_le_of_surjective F.toRingHom hF
      _ = ringKrullDim (MvPolynomial (Fin n) K) := ringKrullDim_eq_of_ringEquiv e.toRingEquiv
      _ = n := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
          zero_add]
        simp

/-- The fibres over field-valued points of a morphism of finite type between affine schemes have
uniformly bounded dimension. -/
theorem exists_topologicalKrullDim_pullback_le_of_isAffine {U W : Scheme.{u}} [IsAffine U]
    [IsAffine W] (h : U ⟶ W) [LocallyOfFiniteType h] :
    ∃ n : ℕ, ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ W),
      topologicalKrullDim (pullback h s : Scheme.{u}) ≤ n := by
  have hφ : h.appTop.hom.FiniteType := by
    have e : Spec.map h.appTop = U.isoSpec.inv ≫ h ≫ W.isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    have : LocallyOfFiniteType (Spec.map h.appTop) := by
      rw [e]
      infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  algebraize [h.appTop.hom]
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hφ
  refine ⟨n, fun K _ s ↦ ?_⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (s ≫ W.isoSpec.hom)
  algebraize [ψ.hom]
  let i : pullback h s ⟶ pullback (Spec.map h.appTop) (Spec.map ψ) :=
    pullback.map _ _ _ _ U.isoSpec.hom (𝟙 _) W.isoSpec.hom
      (Scheme.isoSpec_hom_naturality h).symm (by rw [hψ, Category.id_comp])
  calc topologicalKrullDim (pullback h s : Scheme.{u})
      _ = topologicalKrullDim (pullback (Spec.map h.appTop) (Spec.map ψ) : Scheme.{u}) :=
        IsHomeomorph.topologicalKrullDim_eq _ (asIso i).hom.homeomorph.isHomeomorph
      _ = topologicalKrullDim (Spec (.of (Γ(U, ⊤) ⊗[Γ(W, ⊤)] K))) :=
        IsHomeomorph.topologicalKrullDim_eq _
          (pullbackSpecIso Γ(W, ⊤) Γ(U, ⊤) K).hom.homeomorph.isHomeomorph
      _ = ringKrullDim (Γ(U, ⊤) ⊗[Γ(W, ⊤)] K) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ ≤ n := ringKrullDim_tensorProduct_le_of_surjective n f hf

/-- An empty scheme has dimension `⊥`, below every bound. -/
private lemma topologicalKrullDim_le_of_isEmpty (X : Scheme.{u}) [IsEmpty X] (n : WithBot ℕ∞) :
    topologicalKrullDim X ≤ n :=
  topologicalKrullDim_le_of_iSup_eq_top (fun i : Empty ↦ i.elim) (Subsingleton.elim _ _) n
    fun i ↦ i.elim

/-- Base change of a morphism of finite type between affine schemes along an open immersion
into the target: the fibres over field-valued points of `h ≫ w`, for `w` an open immersion,
have the same bound as those of `h`. -/
private lemma topologicalKrullDim_pullback_comp_le {U W Y : Scheme.{u}} (h : U ⟶ W)
    (w : W ⟶ Y) [IsOpenImmersion w] (n : WithBot ℕ∞)
    (hn : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ W),
      topologicalKrullDim (pullback h s : Scheme.{u}) ≤ n)
    (K : Type u) [Field K] (s : Spec (.of K) ⟶ Y) :
    topologicalKrullDim (pullback (h ≫ w) s : Scheme.{u}) ≤ n := by
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (pullbackRightPullbackFstIso w s h).hom.homeomorph.isHomeomorph]
  by_cases hP : Nonempty (pullback w s : Scheme.{u})
  · have : Function.Surjective (pullback.snd w s) := fun x ↦
      ⟨hP.some, Subsingleton.elim (α := Spec (.of K)) _ _⟩
    have : IsIso (pullback.snd w s) :=
      (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨this⟩⟩
    let i : pullback h (pullback.fst w s) ⟶ pullback h (inv (pullback.snd w s) ≫ pullback.fst w s) :=
      pullback.map _ _ _ _ (𝟙 _) (pullback.snd w s) (𝟙 _) (by simp) (by simp)
    rw [IsHomeomorph.topologicalKrullDim_eq _ (asIso i).hom.homeomorph.isHomeomorph]
    exact hn K _
  · have : IsEmpty (pullback w s : Scheme.{u}) := not_nonempty_iff.mp hP
    have : IsEmpty (pullback h (pullback.fst w s) : Scheme.{u}) :=
      ⟨fun x ↦ isEmptyElim (pullback.snd h (pullback.fst w s) x)⟩
    exact topologicalKrullDim_le_of_isEmpty _ n

/-- **Uniform bound on fibre dimensions.** For `g : Z ⟶ Y` locally of finite type with `Z`
quasi-compact, there is `e : ℕ` with `dim (Z ×_Y Spec K) ≤ e` for every field `K` and every
`Spec K ⟶ Y`. -/
theorem exists_topologicalKrullDim_pullback_le {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [LocallyOfFiniteType g] [CompactSpace Z] :
    ∃ e : ℕ, ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ Y),
      topologicalKrullDim (pullback g s : Scheme.{u}) ≤ e := by
  have hloc (z : Z) : ∃ (U : Z.Opens) (n : ℕ), z ∈ U ∧ ∀ (K : Type u) [Field K]
      (s : Spec (.of K) ⟶ Y), topologicalKrullDim (pullback (U.ι ≫ g) s : Scheme.{u}) ≤ n := by
    obtain ⟨V, hV, hzV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      Y.isBasis_affineOpens) (show g z ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨U, hU, hzU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      Z.isBasis_affineOpens) (show z ∈ g ⁻¹ᵁ V from hzV)
    have : IsAffine U := hU
    have : IsAffine V := hV
    obtain ⟨n, hn⟩ := exists_topologicalKrullDim_pullback_le_of_isAffine (g.resLE V U hUV)
    refine ⟨U, n, hzU, fun K _ s ↦ ?_⟩
    rw [← Scheme.Hom.resLE_comp_ι g hUV]
    exact topologicalKrullDim_pullback_comp_le _ _ _ hn K s
  choose U n hzU hU using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun z ↦ (U z : Set Z))
    (fun z ↦ (U z).isOpen) fun z _ ↦ Set.mem_iUnion.mpr ⟨z, hzU z⟩
  refine ⟨t.sup n, fun K _ s ↦ ?_⟩
  let j (z : t) := pullback.snd (U z).ι (pullback.fst g s)
  refine topologicalKrullDim_le_of_iSup_eq_top (fun z : t ↦ (j z).opensRange) ?_ _
    fun z ↦ ?_
  · refine eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
    obtain ⟨z, hz, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (pullback.fst g s x)))
    refine ⟨⟨z, hz⟩, ?_⟩
    rw [Scheme.Hom.mem_opensRange, ← Set.mem_range, Scheme.Pullback.range_snd]
    simpa using hx
  · calc topologicalKrullDim (j z).opensRange
        _ = topologicalKrullDim (pullback (U z).ι (pullback.fst g s) : Scheme) :=
          (j z).isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range.symm
        _ = topologicalKrullDim (pullback ((U z).ι ≫ g) s : Scheme) :=
          IsHomeomorph.topologicalKrullDim_eq _
            (pullbackRightPullbackFstIso g s (U z).ι).hom.homeomorph.isHomeomorph
        _ ≤ n z := hU z K s
        _ ≤ t.sup n := by exact_mod_cast Finset.le_sup (f := n) z.2

end AlgebraicGeometry
