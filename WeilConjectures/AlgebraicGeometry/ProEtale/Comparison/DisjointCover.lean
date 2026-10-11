/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine

/-!
# Refining pro-étale coverings by a single surjection with a disjoint decomposition

Every covering sieve of an object `U₀` of the affine pro-étale site of a scheme `S` contains
the pieces of a finite disjoint open decomposition of the source of a single surjection
`q : W ⟶ U₀` (`AlgebraicGeometry.Scheme.AffineProEt.exists_singleton_refinement`), and a single
surjection generates a covering sieve
(`AlgebraicGeometry.Scheme.AffineProEt.generate_singleton_toProEt_map_mem`).

Ported from the `proetale` package (`Proetale.Topology.Comparison.Acyclicity`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

namespace AffineProEt

/-- Regard a pro-étale object with pro-affine-étale structure morphism as an object of the
affine pro-étale site. -/
def ofProEt (X : S.ProEt) (hX : proAffineEtale X.hom) : S.AffineProEt :=
  AffineProEt.mk X.hom hX

lemma toProEt_obj_ofProEt (X : S.ProEt) (hX : proAffineEtale X.hom) :
    (AffineProEt.toProEt S).obj (ofProEt X hX) = X :=
  rfl

/-- A variant of `AffineProEt.exists_surjective_factorization` which additionally records
that the open pieces `j i : V i ⟶ W` have pairwise disjoint ranges: `W` is the disjoint
union `Spec (∏ᵢ Γ(Vᵢ))` of the `V i`. -/
lemma exists_surjective_factorization_disjoint {X : S.AffineProEt} {ι : Type u} [Finite ι]
    (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((f i).left.base)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ X) (j : ∀ i, V i ⟶ W),
      Surjective q.left ∧ (∀ i, j i ≫ q = f i) ∧ (∀ i, IsOpenImmersion (j i).left) ∧
      (∀ w : W.left, ∃ i, w ∈ Set.range ((j i).left.base)) ∧
      (Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
        (Set.range ((j l).left.base))) := by
  -- The product of the rings of global sections; `Spec` of it is the disjoint union.
  let R : CommRingCat.{u} := .of (Π i, Γ((V i).left, ⊤))
  let φ : Γ(X.left, ⊤) ⟶ R := CommRingCat.ofHom (RingHom.pi fun i ↦ ((f i).left.appTop).hom)
  have hφ : φ.hom.IndEtale :=
    RingHom.IndEtale.pi _ fun i ↦ indEtale_appTop_of_proAffineEtale (proAffineEtale_hom (f i))
  let q₀ : Spec R ⟶ X.left := Spec.map φ ≫ X.left.isoSpec.inv
  have hq₀ : proAffineEtale q₀ :=
    (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr (proAffineEtale_Spec_iff.mpr hφ)
  let W : S.AffineProEt := mk (q₀ ≫ X.hom) (proAffineEtale.comp_mem _ _ hq₀ X.prop)
  let q : W ⟶ X := MorphismProperty.Over.homMk q₀ rfl trivial
  let e : ∀ i, (V i).left ⟶ Spec R := fun i ↦
    (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))
  have he : ∀ i, e i ≫ q₀ = (f i).left := by
    intro i
    have h1 : φ ≫ CommRingCat.ofHom (Pi.evalRingHom _ i) = (f i).left.appTop := by
      ext x
      rfl
    change ((V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))) ≫
      Spec.map φ ≫ X.left.isoSpec.inv = (f i).left
    rw [Category.assoc, ← Spec.map_comp_assoc, h1, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hw : ∀ i, e i ≫ W.hom = (V i).hom := fun i ↦ by
    change e i ≫ q₀ ≫ X.hom = (V i).hom
    rw [← Category.assoc, he i, MorphismProperty.Over.w (f i)]
  let j : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (e i) (hw i) trivial
  have hcomp : ∀ i, j i ≫ q = f i := by
    intro i
    apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left]
    exact he i
  have hoiSpec (i : ι) : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i))) := by
    rw [← ι_sigmaSpec (fun k ↦ Γ((V k).left, ⊤)) i]
    infer_instance
  have hoi : ∀ i, IsOpenImmersion (j i).left := fun i ↦ by
    have hj : (j i).left = (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := rfl
    rw [hj]
    have := hoiSpec i
    infer_instance
  -- The pieces `j i` factor through `sigmaSpec` via the coproduct inclusions.
  have key : ∀ (i : ι) (c : (V i).left),
      (j i).left c =
        (sigmaSpec fun k ↦ Γ((V k).left, ⊤))
          ((Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i) ((V i).left.isoSpec.hom c)) := by
    intro i c
    have hj : (j i).left = (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := rfl
    calc (j i).left c
        = (Spec.map (CommRingCat.ofHom
            (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)))
            ((V i).left.isoSpec.hom c) := by
          rw [hj]; exact Scheme.Hom.comp_apply _ _ _
      _ = (Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i ≫ sigmaSpec fun k ↦ Γ((V k).left, ⊤))
            ((V i).left.isoSpec.hom c) :=
          congrArg (fun g ↦ g ((V i).left.isoSpec.hom c))
            (ι_sigmaSpec (fun k ↦ Γ((V k).left, ⊤)) i).symm
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤))
            ((Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i) ((V i).left.isoSpec.hom c)) :=
          Scheme.Hom.comp_apply _ _ _
  have hcov : ∀ w : W.left, ∃ i, w ∈ Set.range ((j i).left.base) := by
    intro w
    obtain ⟨p, hp⟩ := (sigmaSpec fun i ↦ Γ((V i).left, ⊤)).surjective w
    obtain ⟨i, y, hy⟩ : ∃ (i : ι) (y : Spec (Γ((V i).left, ⊤))),
        ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i) y = p :=
      ⟨_, (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).covers p⟩
    have h2 : (V i).left.isoSpec.inv ≫ e i =
        Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := by
      change (V i).left.isoSpec.inv ≫ (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) = _
      rw [Iso.inv_hom_id_assoc]
    have hmor : (V i).left.isoSpec.inv ≫ (j i).left =
        (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i ≫
          sigmaSpec fun k ↦ Γ((V k).left, ⊤) := by
      have hj : (j i).left = e i := rfl
      rw [hj, h2, show (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i =
        Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i from rfl, ι_sigmaSpec]
    refine ⟨i, (V i).left.isoSpec.inv y, ?_⟩
    calc (j i).left ((V i).left.isoSpec.inv y)
        = ((V i).left.isoSpec.inv ≫ (j i).left) y := (Scheme.Hom.comp_apply _ _ _).symm
      _ = ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i ≫
            sigmaSpec fun k ↦ Γ((V k).left, ⊤)) y := congrArg (fun g ↦ g y) hmor
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤))
            ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i y) :=
          Scheme.Hom.comp_apply _ _ _
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤)) p := by rw [hy]
      _ = w := hp
  have hq₀surj : Function.Surjective q₀.base := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨(e i).base y, ?_⟩
    calc q₀.base ((e i).base y) = (e i ≫ q₀).base y := rfl
      _ = (f i).left.base y := by rw [he i]
      _ = x := hy
  -- Disjointness of the ranges of the pieces, via disjointness of the coproduct components.
  have hdisj : Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
      (Set.range ((j l).left.base)) := by
    intro k l hkl
    rw [Set.disjoint_left]
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    have hinj : Function.Injective (sigmaSpec fun m ↦ Γ((V m).left, ⊤)).base :=
      (sigmaSpec fun m ↦ Γ((V m).left, ⊤)).isOpenEmbedding.injective
    have heq : (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) k) ((V k).left.isoSpec.hom a) =
        (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) l) ((V l).left.isoSpec.hom b) := by
      apply hinj
      rw [← key k a, ← key l b]
      exact ha.trans hb.symm
    have hd := disjoint_opensRange_sigmaι (fun m ↦ Spec (Γ((V m).left, ⊤))) k l hkl
    have hmem : (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) k) ((V k).left.isoSpec.hom a) ∈
        (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) k).opensRange ⊓
          (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) l).opensRange :=
      ⟨⟨_, rfl⟩, ⟨_, heq.symm⟩⟩
    simpa using hd.le_bot hmem
  exact ⟨W, q, j, ⟨hq₀surj⟩, hcomp, hoi, hcov, hdisj⟩

/-- **(D1)** Every covering sieve of an affine pro-étale object contains a finite jointly
surjective family which factors through a single surjective morphism `q : W ⟶ U₀` whose
source decomposes into finitely many disjoint open pieces mapping into the sieve. -/
lemma exists_singleton_refinement (U₀ : S.AffineProEt)
    {R : Sieve ((AffineProEt.toProEt S).obj U₀)}
    (hR : R ∈ ProEt.topology S ((AffineProEt.toProEt S).obj U₀)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ U₀) (ι : Type u) (_ : Finite ι)
      (V : ι → S.AffineProEt) (j : ∀ k, V k ⟶ W),
      Surjective q.left ∧
      (∀ k, R.arrows ((AffineProEt.toProEt S).map (j k ≫ q))) ∧
      (∀ k, IsOpenImmersion (j k).left) ∧
      (∀ x : W.left, ∃ k, x ∈ Set.range ((j k).left.base)) ∧
      (Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
        (Set.range ((j l).left.base))) := by
  -- The pullback of `R` to the affine pro-étale site is a covering sieve, since the
  -- affine pro-étale site is a dense subsite of the pro-étale site.
  have hR' : R.functorPullback (AffineProEt.toProEt S) ∈ AffineProEt.topology S U₀ :=
    Functor.mem_restrictedTopology_of_functorPushforward_mem
      (Functor.IsCoverDense.functorPullback_pushforward_covering
        (G := AffineProEt.toProEt S) (K := ProEt.topology S) ⟨R, hR⟩)
  obtain ⟨ι, _, V, f, hf, hsurj⟩ := exists_finite_jointly_surjective_of_mem_topology hR'
  obtain ⟨W, q, j, hq, hcomp, hoi, hcov, hdisj⟩ :=
    exists_surjective_factorization_disjoint V f hsurj
  refine ⟨W, q, ι, ‹_›, V, j, hq, fun k ↦ ?_, hoi, hcov, hdisj⟩
  rw [hcomp k]
  exact hf k

/-- A surjective morphism in the affine pro-étale site generates a covering sieve of the
pro-étale topology. -/
lemma generate_singleton_toProEt_map_mem {W U₀ : S.AffineProEt} (q : W ⟶ U₀)
    (hq : Surjective q.left) :
    Sieve.generate (Presieve.singleton ((AffineProEt.toProEt S).map q)) ∈
      ProEt.topology S ((AffineProEt.toProEt S).obj U₀) := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  simp only [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_singleton,
    AffineProEt.toProEt_map,
    Functor.comp_map, ProEt.forget_map, Over.forget_map]
  have : Surjective q.left := hq
  exact q.left.singleton_mem_propQCPrecoverage inferInstance

end AffineProEt

end AlgebraicGeometry.Scheme
