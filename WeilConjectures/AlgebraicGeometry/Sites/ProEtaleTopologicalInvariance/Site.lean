/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleTopologicalInvariance.CoverDense
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Reduction
public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Cover-density of base change along a universal homeomorphism on pro-étale sites

Let `r : X ⟶ Y` be a universal homeomorphism. We show that every scheme `U` weakly étale over
`X` is covered, in the pro-étale topology, by schemes of the form `V ×_Y X` with `V` weakly
étale over `Y`: the base change functor `Y.ProEt ⥤ X.ProEt` is cover-dense. This is the
scheme-theoretic form of
`AlgebraicGeometry.Algebra.IsUniversalHomeomorphism.exists_weaklyEtale_comap_surjective`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_weaklyEtale_surjective_of_isAffine`: for `X`, `Y` and
  `U` affine there is an affine `V` weakly étale over `Y` and a surjective `X`-morphism
  `V ×_Y X ⟶ U`.
- `AlgebraicGeometry.Scheme.Hom.exists_weaklyEtale_hom_mem_range`: every point of a scheme
  weakly étale over `X` lies in an affine open which is the image of such a surjection.
- `AlgebraicGeometry.Scheme.ProEt.isCoverDense_overPullback`: the base change functor
  `Y.ProEt ⥤ X.ProEt` along a universal homeomorphism is cover-dense.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r]

/-- **Cover-density, affine case**: for a universal homeomorphism `r : X ⟶ Y` of affine schemes
and an affine scheme `U` weakly étale over `X`, there is an affine scheme `V` weakly étale over
`Y` and a surjective `X`-morphism `V ×_Y X ⟶ U`. -/
theorem exists_weaklyEtale_surjective_of_isAffine [IsAffine X] [IsAffine Y] {U : Scheme.{u}}
    [IsAffine U] (g : U ⟶ X) [WeaklyEtale g] :
    ∃ (V : Scheme.{u}) (_ : IsAffine V) (p : V ⟶ Y) (_ : WeaklyEtale p)
      (h : pullback p r ⟶ U), h ≫ g = pullback.snd p r ∧ Function.Surjective h := by
  -- the rings `A = Γ(Y)`, `B = Γ(X)` and `S = Γ(U)`
  let _ : Algebra Γ(Y, ⊤) Γ(X, ⊤) := r.appTop.hom.toAlgebra
  let _ : Algebra Γ(X, ⊤) Γ(U, ⊤) := g.appTop.hom.toAlgebra
  have hr : r = X.isoSpec.hom ≫ Spec.map r.appTop ≫ Y.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hrS : Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤))) =
      X.isoSpec.inv ≫ r ≫ Y.isoSpec.hom := by
    rw [hr]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
    rfl
  have : _root_.Algebra.IsUniversalHomeomorphism Γ(Y, ⊤) Γ(X, ⊤) :=
    ⟨by rw [hrS]; infer_instance⟩
  have : _root_.Algebra.WeaklyEtale Γ(X, ⊤) Γ(U, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @WeaklyEtale) (Q := RingHom.WeaklyEtale)).mp
      inferInstance
  -- the ring-theoretic statement
  obtain ⟨T, _, _, hT, φ, hφ, hsurj⟩ :=
    Algebra.IsUniversalHomeomorphism.exists_weaklyEtale_comap_surjective Γ(Y, ⊤) Γ(X, ⊤)
      Γ(U, ⊤)
  let p : Spec (.of T) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) T)) ≫ Y.isoSpec.inv
  -- the identification `pullback p r ≅ Spec (T ⊗[Γ(Y)] Γ(X))`
  let m : pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) T)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤)))) ⟶ pullback p r :=
    pullback.map _ _ _ _ (𝟙 _) X.isoSpec.inv Y.isoSpec.inv (by simp [p])
      (by rw [hrS]; simp)
  let h : pullback p r ⟶ U :=
    inv m ≫ (pullbackSpecIso Γ(Y, ⊤) T Γ(X, ⊤)).hom ≫ Spec.map (CommRingCat.ofHom φ) ≫
      U.isoSpec.inv
  refine ⟨Spec (.of T), inferInstance, p, inferInstance, h, ?_, ?_⟩
  · have h₁ : Spec.map (CommRingCat.ofHom φ) ≫ U.isoSpec.inv ≫ g =
        Spec.map (CommRingCat.ofHom
          (_root_.Algebra.TensorProduct.includeRight.toRingHom :
            Γ(X, ⊤) →+* T ⊗[Γ(Y, ⊤)] Γ(X, ⊤))) ≫ X.isoSpec.inv := by
      rw [← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp, ← hφ]
      rfl
    have h₂ : m ≫ pullback.snd p r = pullback.snd _ _ ≫ X.isoSpec.inv := pullback.lift_snd _ _ _
    have h₃ : (pullbackSpecIso Γ(Y, ⊤) T Γ(X, ⊤)).hom ≫ Spec.map (CommRingCat.ofHom
        (_root_.Algebra.TensorProduct.includeRight.toRingHom :
          Γ(X, ⊤) →+* T ⊗[Γ(Y, ⊤)] Γ(X, ⊤))) = pullback.snd _ _ :=
      pullbackSpecIso_hom_snd _ _ _
    simp only [h, Category.assoc, h₁]
    rw [← Category.assoc (pullbackSpecIso _ _ _).hom, h₃, IsIso.inv_comp_eq, h₂]
  · have : Surjective (Spec.map (CommRingCat.ofHom φ)) := ⟨hsurj⟩
    exact h.surjective

/-- **Cover-density, local form**: for a universal homeomorphism `r : X ⟶ Y`, every point `u` of
a scheme `U` weakly étale over `X` has an affine open neighbourhood `U₀` which is the image of a
surjective `X`-morphism `V ×_Y X ⟶ U₀` with `V` affine and weakly étale over `Y`. -/
theorem exists_weaklyEtale_surjective {U : Scheme.{u}} (g : U ⟶ X) [WeaklyEtale g] (u : U) :
    ∃ (U₀ : U.Opens) (_ : IsAffineOpen U₀) (_ : u ∈ U₀) (V : Scheme.{u}) (_ : IsAffine V)
      (p : V ⟶ Y) (_ : WeaklyEtale p) (h : pullback p r ⟶ U₀),
      h ≫ U₀.ι ≫ g = pullback.snd p r ∧ Function.Surjective h := by
  obtain ⟨_, ⟨(Y₀ : Y.Opens), hY₀, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (r (g u))) isOpen_univ
  have hX₀ : IsAffineOpen (r ⁻¹ᵁ Y₀) := hY₀.preimage r
  obtain ⟨_, ⟨(U₀ : U.Opens), hU₀, rfl⟩, hu, hle⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (show u ∈ g ⁻¹ᵁ (r ⁻¹ᵁ Y₀) from hy)
      (g ⁻¹ᵁ (r ⁻¹ᵁ Y₀)).isOpen
  have : IsAffine (↑(r ⁻¹ᵁ Y₀) : Scheme.{u}) := hX₀
  have : IsAffine (↑Y₀ : Scheme.{u}) := hY₀
  have : IsAffine (↑U₀ : Scheme.{u}) := hU₀
  obtain ⟨V, _, p₀, _, h₀, hh₀, hsurj⟩ :=
    exists_weaklyEtale_surjective_of_isAffine (r ∣_ Y₀) (g.resLE (r ⁻¹ᵁ Y₀) U₀ hle)
  have H := (IsPullback.of_hasPullback p₀ (r ∣_ Y₀)).paste_vert (isPullback_morphismRestrict r Y₀)
  refine ⟨U₀, hU₀, hu, V, inferInstance, p₀ ≫ Y₀.ι, inferInstance, H.isoPullback.inv ≫ h₀, ?_,
    ?_⟩
  · rw [Category.assoc, ← Scheme.Hom.resLE_comp_ι g hle, ← Category.assoc h₀, hh₀,
      H.isoPullback_inv_snd]
  · exact hsurj.comp H.isoPullback.inv.surjective

end Scheme.Hom

namespace Scheme.ProEt

variable {X : Scheme.{u}}

/-- A sieve on `U : X.ProEt` containing a surjective quasi-compact morphism is covering. -/
lemma mem_topology_of_surjective {U V : X.ProEt} (S : Sieve U) (f : V ⟶ U) [Surjective f.left]
    [QuasiCompact f.left] (hf : S f) : S ∈ topology X U := by
  rw [mem_topology_iff]
  refine ⟨Presieve.singleton f, ?_, fun _ _ h ↦ by cases h; exact hf⟩
  rw [mem_precoverage_iff, Presieve.map_singleton]
  have : WeaklyEtale f.left := by
    have : WeaklyEtale (f.left ≫ U.hom) := by rw [MorphismProperty.Over.w f]; infer_instance
    exact WeaklyEtale.of_comp f.left U.hom
  have : WeaklyEtale ((ProEt.forget X ⋙ CategoryTheory.Over.forget X).map f) := this
  refine ⟨Hom.singleton_mem_qcPrecoverage f.left, ?_⟩
  rw [← Presieve.ofArrows_pUnit.{0}, ofArrows_mem_precoverage_iff]
  exact ⟨fun x ↦ ⟨⟨⟩, f.left.surjective x⟩, fun _ ↦ inferInstance⟩

/-- A sieve on `U : X.ProEt` is covering if every point of `U` has an open neighbourhood `U₀`
which is the image of a surjective quasi-compact morphism `V ⟶ U₀` lying in the sieve. -/
lemma mem_topology_of_forall_exists {U : X.ProEt} (S : Sieve U)
    (H : ∀ u : U.left, ∃ (U₀ : U.left.Opens) (_ : u ∈ U₀) (V : X.ProEt)
      (f : V ⟶ ofOpenImmersion U U₀.ι), Surjective f.left ∧ QuasiCompact f.left ∧
        S (f ≫ ofOpenImmersionHom U U₀.ι)) :
    S ∈ topology X U := by
  choose U₀ hu V f hsurj hqc hS using H
  let R : Sieve U := Sieve.ofArrows (fun u ↦ ofOpenImmersion U (U₀ u).ι)
    (fun u ↦ ofOpenImmersionHom U (U₀ u).ι)
  have hR : R ∈ topology X U :=
    mem_topology_of_openImmersion R (fun u ↦ (U₀ u).ι) (fun x ↦ ⟨x, by simpa using hu x⟩)
      (fun u ↦ Sieve.ofArrows_mk _ _ u)
  refine GrothendieckTopology.transitive _ hR S fun W g hg ↦ ?_
  obtain ⟨u, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  rw [Sieve.pullback_comp]
  refine GrothendieckTopology.pullback_stable _ a ?_
  have := hsurj u
  have := hqc u
  exact mem_topology_of_surjective _ (f u) (hS u)

end Scheme.ProEt

namespace Scheme.ProEt

variable {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r]

/-- **Cover-density of base change along a universal homeomorphism**: every scheme weakly
étale over `X` is covered, in the pro-étale topology, by base changes of schemes weakly étale
over `Y`. -/
instance isCoverDense_overPullback :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).IsCoverDense (topology X) where
  is_cover U := by
    refine mem_topology_of_forall_exists _ fun u ↦ ?_
    obtain ⟨U₀, hU₀, hu, V, _, p, _, h, hh, hsurj⟩ := r.exists_weaklyEtale_surjective U.hom u
    have : IsAffine (U₀ : Scheme.{u}) := hU₀
    let f : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ r).obj (ProEt.mk p) ⟶
        ofOpenImmersion U U₀.ι :=
      MorphismProperty.Over.homMk h hh
    have : IsAffine (pullback p r) := isAffine_of_isAffineHom (pullback.fst p r)
    have : QuasiCompact f.left := (inferInstance : QuasiCompact h)
    refine ⟨U₀, hu, _, f, ⟨hsurj⟩, inferInstance, ?_⟩
    exact ⟨⟨ProEt.mk p, 𝟙 _, f ≫ ofOpenImmersionHom U U₀.ι, by simp⟩⟩

end Scheme.ProEt

end AlgebraicGeometry
