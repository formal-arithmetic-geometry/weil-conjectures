/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.VeroneseGradedRing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Tactic.ApplyFun

/-! # The canonical isomorphism of Proj with a Veronese Proj

Source: Stacks Project, Tag 0B5J.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (𝒜 : ℕ → Submodule k R) [GradedRing 𝒜] (d : ℕ+)

private abbrev S := GradedAlgebra.veroneseSubring 𝒜 d
private abbrev ℬ := GradedAlgebra.veroneseGrade 𝒜 d

private noncomputable def localizationMap (s : S 𝒜 d) :
    Localization.Away s →+* Localization.Away (s : R) :=
  IsLocalization.map (M := .powers s) (T := .powers (s : R))
    (Localization.Away (s : R)) (S 𝒜 d).subtype
    (Submonoid.powers_le.mpr ⟨1, by simp⟩)

private noncomputable def chartMap (s : S 𝒜 d) : Away (ℬ 𝒜 d) s →+* Away 𝒜 (s : R) where
  toFun := Quotient.map'
    (fun c => (⟨c.deg * (d : ℕ), ⟨(c.num : S 𝒜 d), c.num.2⟩,
      ⟨(c.den : S 𝒜 d), c.den.2⟩, by
        obtain ⟨n, hn⟩ := c.den_mem
        exact ⟨n, congrArg (fun a : S 𝒜 d => (a : R)) hn⟩⟩ :
        NumDenSameDeg 𝒜 (.powers (s : R))))
    (by
      intro a b hab
      change a.embedding = b.embedding at hab
      apply_fun localizationMap 𝒜 d s at hab
      change _ = _
      simpa only [NumDenSameDeg.embedding, Localization.mk_eq_mk',
        localizationMap, IsLocalization.map_mk', map_pow, Subring.subtype_apply] using hab)
  map_one' := by
    apply val_injective
    change Localization.mk 1 _ = val (1 : Away 𝒜 (s : R))
    simp
  map_zero' := by
    apply val_injective
    change Localization.mk 0 _ = val (0 : Away 𝒜 (s : R))
    simp only [val_zero, Localization.mk_zero]
  map_add' := by
    intro a b
    induction a using Quotient.inductionOn with | _ a =>
      induction b using Quotient.inductionOn with | _ b =>
        apply val_injective
        simp only [← mk_add, Quotient.map'_mk'', val_mk, NumDenSameDeg.num_add,
          NumDenSameDeg.den_add]
        rfl
  map_mul' := by
    intro a b
    induction a using Quotient.inductionOn with | _ a =>
      induction b using Quotient.inductionOn with | _ b =>
        apply val_injective
        simp only [← mk_mul, Quotient.map'_mk'', val_mk, NumDenSameDeg.num_mul,
          NumDenSameDeg.den_mul]
        rfl

private theorem chartMap_mk (m : ℕ) (s : S 𝒜 d) (hs : s ∈ ℬ 𝒜 d m)
    (q : ℕ) (a : S 𝒜 d) (ha : a ∈ ℬ 𝒜 d (q • m)) :
    chartMap 𝒜 d s (Away.mk _ hs q a ha) =
      Away.mk 𝒜 hs q (a : R) (by
        change (a : R) ∈ 𝒜 ((q • m) * (d : ℕ)) at ha
        simpa only [smul_eq_mul, Nat.mul_assoc] using ha) := by
  apply val_injective
  rfl

private theorem chartMap_bijective (m : ℕ) (s : S 𝒜 d) (hs : s ∈ ℬ 𝒜 d m) :
    Function.Bijective (chartMap 𝒜 d s) := by
  constructor
  · intro a b hab
    apply val_injective
    have hinj : Function.Injective
        (localizationMap 𝒜 d s) := by
      have : IsLocalization ((Submonoid.powers s).map (S 𝒜 d).subtype)
          (Localization.Away (s : R)) := by
        rw [Submonoid.map_powers]
        change IsLocalization (.powers (s : R)) (Localization.Away (s : R))
        infer_instance
      exact IsLocalization.map_injective_of_injective (g := (S 𝒜 d).subtype)
        (.powers s) (Localization.Away s) (Localization.Away (s : R))
        Subtype.val_injective
    apply hinj
    obtain ⟨a, rfl⟩ := HomogeneousLocalization.mk_surjective a
    obtain ⟨b, rfl⟩ := HomogeneousLocalization.mk_surjective b
    simpa only [chartMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Quotient.map'_mk'', val_mk, Localization.mk_eq_mk', localizationMap,
      IsLocalization.map_mk', Subring.subtype_apply] using congrArg HomogeneousLocalization.val hab
  · intro z
    obtain ⟨q, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs z
    have ha' : a ∈ 𝒜 ((q • m) * (d : ℕ)) := by
      simpa only [smul_eq_mul, Nat.mul_assoc] using ha
    have hamem : a ∈ S 𝒜 d := Subring.subset_closure (Set.mem_iUnion.mpr ⟨q • m, ha'⟩)
    refine ⟨Away.mk (ℬ 𝒜 d) hs q ⟨a, hamem⟩ ha', ?_⟩
    apply val_injective
    rfl

private noncomputable def chartEquiv (m : ℕ) (s : S 𝒜 d) (hs : s ∈ ℬ 𝒜 d m) :
    Away (ℬ 𝒜 d) s ≃+* Away 𝒜 (s : R) :=
  RingEquiv.ofBijective (chartMap 𝒜 d s) (chartMap_bijective 𝒜 d m s hs)

private theorem chartMap_awayMap {m n : ℕ} {s t : S 𝒜 d}
    (hs : s ∈ ℬ 𝒜 d m) (ht : t ∈ ℬ 𝒜 d n) {u : S 𝒜 d} (hu : u = s * t) :
    (chartMap 𝒜 d u).comp (awayMap (ℬ 𝒜 d) ht hu) =
      (awayMap 𝒜 ht (congrArg Subtype.val hu)).comp (chartMap 𝒜 d s) := by
  apply RingHom.ext
  intro z
  obtain ⟨q, a, ha, rfl⟩ := Away.mk_surjective (ℬ 𝒜 d) hs z
  apply val_injective
  simp only [RingHom.comp_apply, awayMap_mk, chartMap_mk, Away.val_mk]
  rfl

private abbrev Index := Σ m : ℕ+, ℬ 𝒜 d (m : ℕ)

private abbrev rChart (i : Index 𝒜 d) := Away 𝒜 (i.2 : R)
private abbrev sChart (i : Index 𝒜 d) := Away (ℬ 𝒜 d) (i.2 : S 𝒜 d)

private noncomputable abbrev rι (i : Index 𝒜 d) : Spec (.of (rChart 𝒜 d i)) ⟶ Proj 𝒜 :=
  Proj.awayι 𝒜 (i.2 : R) i.2.2 (Nat.mul_pos i.1.pos d.pos)

private noncomputable abbrev sι (i : Index 𝒜 d) :
    Spec (.of (sChart 𝒜 d i)) ⟶ Proj (ℬ 𝒜 d) :=
  Proj.awayι (ℬ 𝒜 d) (i.2 : S 𝒜 d) i.2.2 i.1.pos

private noncomputable abbrev α (i : Index 𝒜 d) :
    sChart 𝒜 d i ≃+* rChart 𝒜 d i := chartEquiv 𝒜 d i.1 i.2 i.2.2

private noncomputable def rCover : (Proj 𝒜).OpenCover :=
  Scheme.Cover.mkOfCovers (Index 𝒜 d) (fun i => Spec (.of (rChart 𝒜 d i))) (rι 𝒜 d)
    (by
      intro x
      obtain ⟨i, y, hy⟩ := (Proj.affineOpenCover 𝒜).openCover.exists_eq x
      let f : R := i.2
      have hf : f ∈ 𝒜 (i.1 : ℕ) := i.2.2
      have hpow : f ^ (d : ℕ) ∈ 𝒜 ((i.1 : ℕ) * (d : ℕ)) := by
        simpa only [smul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded (d : ℕ) hf
      let s : S 𝒜 d := ⟨f ^ (d : ℕ),
        Subring.subset_closure (Set.mem_iUnion.mpr ⟨i.1, hpow⟩)⟩
      have hs : s ∈ ℬ 𝒜 d (i.1 : ℕ) := hpow
      have hx : x ∈ Proj.basicOpen 𝒜 f := by
        rw [← hy]
        exact (Proj.opensRange_awayι 𝒜 f hf i.1.pos).le ⟨y, rfl⟩
      have hx' : x ∈ (rι 𝒜 d ⟨i.1, ⟨s, hs⟩⟩).opensRange := by
        rw [Proj.opensRange_awayι]
        change x ∈ Proj.basicOpen 𝒜 (f ^ (d : ℕ))
        rwa [Proj.basicOpen_pow 𝒜 f (d : ℕ) d.pos]
      exact ⟨⟨i.1, ⟨s, hs⟩⟩, hx'⟩)

private noncomputable abbrev sCover : (Proj (ℬ 𝒜 d)).OpenCover :=
  (Proj.affineOpenCover (ℬ 𝒜 d)).openCover

private noncomputable def forward (i : Index 𝒜 d) :
    Spec (.of (rChart 𝒜 d i)) ⟶ Proj (ℬ 𝒜 d) :=
  Spec.map (CommRingCat.ofHom (α 𝒜 d i).toRingHom) ≫ sι 𝒜 d i

private noncomputable def backward (i : Index 𝒜 d) :
    Spec (.of (sChart 𝒜 d i)) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (α 𝒜 d i).symm.toRingHom) ≫ rι 𝒜 d i

private theorem forward_compatible (i j : Index 𝒜 d) :
    pullback.fst (rι 𝒜 d i) (rι 𝒜 d j) ≫ forward 𝒜 d i =
      pullback.snd (rι 𝒜 d i) (rι 𝒜 d j) ≫ forward 𝒜 d j := by
  rw [← cancel_epi
    (Proj.pullbackAwayιIso 𝒜 i.2.2 (Nat.mul_pos i.1.pos d.pos)
      j.2.2 (Nat.mul_pos j.1.pos d.pos) rfl).inv]
  change (Proj.pullbackAwayιIso 𝒜 i.2.2 (Nat.mul_pos i.1.pos d.pos)
    j.2.2 (Nat.mul_pos j.1.pos d.pos) rfl).inv ≫
      pullback.fst _ _ ≫ forward 𝒜 d i =
    (Proj.pullbackAwayιIso 𝒜 i.2.2 (Nat.mul_pos i.1.pos d.pos)
    j.2.2 (Nat.mul_pos j.1.pos d.pos) rfl).inv ≫
      pullback.snd _ _ ≫ forward 𝒜 d j
  rw [Proj.pullbackAwayιIso_inv_fst_assoc, Proj.pullbackAwayιIso_inv_snd_assoc]
  dsimp only [forward]
  let u : S 𝒜 d := i.2 * j.2
  have hu : u ∈ ℬ 𝒜 d ((i.1 : ℕ) + j.1) :=
    SetLike.mul_mem_graded i.2.2 j.2.2
  have hleft := chartMap_awayMap 𝒜 d i.2.2 j.2.2 (u := u) rfl
  have hright := chartMap_awayMap 𝒜 d j.2.2 i.2.2 (u := u) (mul_comm _ _)
  change Spec.map (CommRingCat.ofHom (awayMap 𝒜 j.2.2 rfl)) ≫
      Spec.map (CommRingCat.ofHom (chartMap 𝒜 d (i.2 : S 𝒜 d))) ≫ sι 𝒜 d i =
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 i.2.2 (mul_comm _ _))) ≫
      Spec.map (CommRingCat.ofHom (chartMap 𝒜 d (j.2 : S 𝒜 d))) ≫ sι 𝒜 d j
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← hleft,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← hright,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι]
  unfold Proj.awayι Proj.basicOpenIsoSpec
  rfl

private theorem chartInverse_awayMap {m n : ℕ} {s t : S 𝒜 d}
    (hs : s ∈ ℬ 𝒜 d m) (ht : t ∈ ℬ 𝒜 d n) {u : S 𝒜 d} (hu : u = s * t) :
    ((chartEquiv 𝒜 d (m + n) u (hu ▸ SetLike.mul_mem_graded hs ht)).symm.toRingHom).comp
        (awayMap 𝒜 ht (congrArg Subtype.val hu)) =
      (awayMap (ℬ 𝒜 d) ht hu).comp (chartEquiv 𝒜 d m s hs).symm.toRingHom := by
  apply RingHom.ext
  intro z
  apply (chartEquiv 𝒜 d (m + n) u (hu ▸ SetLike.mul_mem_graded hs ht)).injective
  change (chartEquiv 𝒜 d (m + n) u (hu ▸ SetLike.mul_mem_graded hs ht))
    ((chartEquiv 𝒜 d (m + n) u (hu ▸ SetLike.mul_mem_graded hs ht)).symm ((awayMap 𝒜 ht _) z)) =
    (chartEquiv 𝒜 d (m + n) u (hu ▸ SetLike.mul_mem_graded hs ht))
      ((awayMap (ℬ 𝒜 d) ht hu) ((chartEquiv 𝒜 d m s hs).symm z))
  rw [RingEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (chartMap_awayMap 𝒜 d hs ht hu)
    ((chartEquiv 𝒜 d m s hs).symm z)
  change _ = (chartEquiv 𝒜 d (m + n) u (hu ▸ SetLike.mul_mem_graded hs ht)) _
  change (chartEquiv 𝒜 d (m + n) u (hu ▸ SetLike.mul_mem_graded hs ht)) _ =
    awayMap 𝒜 ht (congrArg Subtype.val hu) ((chartEquiv 𝒜 d m s hs)
      ((chartEquiv 𝒜 d m s hs).symm z)) at h
  rw [RingEquiv.apply_symm_apply] at h
  simpa only [RingEquiv.coe_toRingHom] using h.symm

private theorem backward_compatible (i j : Index 𝒜 d) :
    pullback.fst (sι 𝒜 d i) (sι 𝒜 d j) ≫ backward 𝒜 d i =
      pullback.snd (sι 𝒜 d i) (sι 𝒜 d j) ≫ backward 𝒜 d j := by
  rw [← cancel_epi (Proj.pullbackAwayιIso (ℬ 𝒜 d) i.2.2 i.1.pos
    j.2.2 j.1.pos rfl).inv]
  simp only [Proj.pullbackAwayιIso_inv_fst_assoc,
    Proj.pullbackAwayιIso_inv_snd_assoc, backward]
  have hleft := chartInverse_awayMap 𝒜 d i.2.2 j.2.2 rfl
  have hright := chartInverse_awayMap 𝒜 d j.2.2 i.2.2 (mul_comm (i.2 : S 𝒜 d) j.2)
  change Spec.map (CommRingCat.ofHom (awayMap (ℬ 𝒜 d) j.2.2 rfl)) ≫
      Spec.map (CommRingCat.ofHom (chartEquiv 𝒜 d i.1 i.2 i.2.2).symm.toRingHom) ≫
        rι 𝒜 d i =
    Spec.map (CommRingCat.ofHom (awayMap (ℬ 𝒜 d) i.2.2 (mul_comm _ _))) ≫
      Spec.map (CommRingCat.ofHom (chartEquiv 𝒜 d j.1 j.2 j.2.2).symm.toRingHom) ≫
        rι 𝒜 d j
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← hleft,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← hright,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι]
  unfold chartEquiv Proj.awayι Proj.basicOpenIsoSpec
  rfl

private noncomputable def projForward : Proj 𝒜 ⟶ Proj (ℬ 𝒜 d) :=
  (rCover 𝒜 d).glueMorphisms (forward 𝒜 d) (forward_compatible 𝒜 d)

private noncomputable def projBackward : Proj (ℬ 𝒜 d) ⟶ Proj 𝒜 :=
  (sCover 𝒜 d).glueMorphisms (backward 𝒜 d) (backward_compatible 𝒜 d)

private theorem rι_forward (i : Index 𝒜 d) :
    rι 𝒜 d i ≫ projForward 𝒜 d = forward 𝒜 d i :=
  (rCover 𝒜 d).ι_glueMorphisms _ _ i

private theorem sι_backward (i : Index 𝒜 d) :
    sι 𝒜 d i ≫ projBackward 𝒜 d = backward 𝒜 d i :=
  (sCover 𝒜 d).ι_glueMorphisms _ _ i

private noncomputable def veroneseIso : Proj 𝒜 ≅ Proj (ℬ 𝒜 d) where
  hom := projForward 𝒜 d
  inv := projBackward 𝒜 d
  hom_inv_id := by
    apply (rCover 𝒜 d).hom_ext
    intro i
    change rι 𝒜 d i ≫ _ = _
    rw [← Category.assoc, rι_forward, forward, Category.assoc, sι_backward,
      backward, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      RingEquiv.toRingHom_comp_symm_toRingHom]
    simp only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
    rfl
  inv_hom_id := by
    apply (sCover 𝒜 d).hom_ext
    intro i
    change sι 𝒜 d i ≫ _ = _
    rw [← Category.assoc, sι_backward, backward, Category.assoc, rι_forward,
      forward, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      RingEquiv.symm_toRingHom_comp_toRingHom]
    simp

/-- Proj is unchanged by a positive Veronese regrading, with its canonical chart maps.
Source: Stacks Project, Tag 0B5J (blueprint: lem-sfb-veronese-proj-iso).

Proof: For a homogeneous Veronese element, the inclusion of rings identifies the two
homogeneous localizations: a numerator of degree a multiple of its degree belongs to
that Veronese ring, and injectivity follows from injectivity of localization of a
subring. The identifications commute with localization at another homogeneous element.
The original Proj is covered by these charts, since every positive homogeneous element
has its d-th power in the Veronese ring. Glue the chart maps and their inverses; the
composites are identities on every chart. -/
theorem exists_veronese_proj_iso :
    ∃ e : Proj 𝒜 ≅ Proj (GradedAlgebra.veroneseGrade 𝒜 d),
      ∀ (m : ℕ) (s : GradedAlgebra.veroneseSubring 𝒜 d)
        (hs : s ∈ GradedAlgebra.veroneseGrade 𝒜 d m) (hm : 0 < m),
        ∃ α : Away (GradedAlgebra.veroneseGrade 𝒜 d) s →+* Away 𝒜 (s : R),
          (∀ (q : ℕ) (a : GradedAlgebra.veroneseSubring 𝒜 d)
              (ha : a ∈ GradedAlgebra.veroneseGrade 𝒜 d (q • m)),
            (α (Away.mk _ hs q a ha)).val =
              (Localization.mk (a : R) ⟨(s : R) ^ q, ⟨q, rfl⟩⟩ :
                Localization.Away (s : R))) ∧
          Proj.awayι 𝒜 (s : R) hs (Nat.mul_pos hm d.pos) ≫ e.hom =
            Spec.map (CommRingCat.ofHom α) ≫
              Proj.awayι (GradedAlgebra.veroneseGrade 𝒜 d) s hs hm := by
  refine ⟨veroneseIso 𝒜 d, fun m s hs hm => ⟨chartMap 𝒜 d s, ?_, ?_⟩⟩
  · intro q a ha
    rfl
  · exact rι_forward 𝒜 d ⟨⟨m, hm⟩, ⟨s, hs⟩⟩

end AlgebraicGeometry
