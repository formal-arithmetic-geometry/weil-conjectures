/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Geometry of the codiagonal of a coproduct of copies of a scheme

For a scheme `V` and a `u`-small type `S`, the codiagonal `∐_{s : S} V ⟶ V` is etale,
separated and surjective for nonempty `S`. Moreover every quasi-compact scheme admitting an open
immersion into a coproduct of affine schemes is quasi-affine.

Source: Stacks Project, Tags 03YW, 01P6 and 0AP6.
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The codiagonal of a coproduct of copies of a scheme is etale: each component chart is the
identity. Source: Stacks Project, Tag 03YW. -/
lemma etale_sigmaDesc_id (V : Scheme.{u}) (S : Type w) [Small.{u} S] :
    Etale (Sigma.desc fun _ : S ↦ 𝟙 V : (∐ fun _ : S ↦ V) ⟶ V) :=
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

/-- The codiagonal of a nonempty coproduct of copies of a scheme is surjective, since a
labelled component is a section. Source: Stacks Project, Tag 03YW. -/
lemma surjective_sigmaDesc_id (V : Scheme.{u}) (S : Type w) [Small.{u} S] [Nonempty S] :
    Surjective (Sigma.desc fun _ : S ↦ 𝟙 V : (∐ fun _ : S ↦ V) ⟶ V) := by
  have : Surjective (Sigma.ι (fun _ : S ↦ V) (Classical.arbitrary S) ≫
      (Sigma.desc fun _ : S ↦ 𝟙 V : (∐ fun _ : S ↦ V) ⟶ V)) := by
    rw [Sigma.ι_desc]
    infer_instance
  exact .of_comp (Sigma.ι (fun _ : S ↦ V) (Classical.arbitrary S)) _

/-- Every point of a coproduct of schemes lies in the image of one of the coprojections.
Source: Stacks Project, Tag 01JA. -/
lemma exists_sigmaι_eq {σ : Type w} [Small.{u} σ] (g : σ → Scheme.{u}) (x : (∐ g : Scheme.{u})) :
    ∃ i y, Sigma.ι g i y = x := by
  obtain ⟨y, hy⟩ := (sigmaOpenCover g).covers x
  exact ⟨_, y, hy⟩

/-- A point of the self-fibre product of the codiagonal of a coproduct of copies of a scheme
whose two projections lie in the same component is in the range of the diagonal.
Source: Stacks Project, Tag 03YW. -/
lemma mem_range_diagonal_sigmaDesc_id (V : Scheme.{u}) {S : Type w} [Small.{u} S] (s : S)
    (z : ↥(pullback (Sigma.desc fun _ : S ↦ 𝟙 V : (∐ fun _ : S ↦ V) ⟶ V)
      (Sigma.desc fun _ : S ↦ 𝟙 V : (∐ fun _ : S ↦ V) ⟶ V)))
    (h₁ : pullback.fst (Sigma.desc fun _ : S ↦ 𝟙 V : (∐ fun _ : S ↦ V) ⟶ V)
      (Sigma.desc fun _ : S ↦ 𝟙 V) z ∈ Set.range (Sigma.ι (fun _ : S ↦ V) s))
    (h₂ : pullback.snd (Sigma.desc fun _ : S ↦ 𝟙 V : (∐ fun _ : S ↦ V) ⟶ V)
      (Sigma.desc fun _ : S ↦ 𝟙 V) z ∈ Set.range (Sigma.ι (fun _ : S ↦ V) s)) :
    z ∈ Set.range (pullback.diagonal (Sigma.desc fun _ : S ↦ 𝟙 V : (∐ fun _ : S ↦ V) ⟶ V)) := by
  have e : 𝟙 V ≫ 𝟙 V = Sigma.ι (fun _ : S ↦ V) s ≫ Sigma.desc fun _ : S ↦ 𝟙 V := by simp
  obtain ⟨w, rfl⟩ : z ∈ Set.range (pullback.map (𝟙 V) (𝟙 V) (Sigma.desc fun _ : S ↦ 𝟙 V)
      (Sigma.desc fun _ : S ↦ 𝟙 V)
      (Sigma.ι (fun _ : S ↦ V) s) (Sigma.ι (fun _ : S ↦ V) s) (𝟙 V) e e) := by
    rw [Scheme.Pullback.range_map]
    exact ⟨h₁, h₂⟩
  obtain ⟨v, rfl⟩ := (pullback.diagonal (𝟙 V)).surjective w
  refine ⟨Sigma.ι (fun _ : S ↦ V) s v, ?_⟩
  have hcomp : Sigma.ι (fun _ : S ↦ V) s ≫ pullback.diagonal (Sigma.desc fun _ : S ↦ 𝟙 V) =
      pullback.diagonal (𝟙 V) ≫ pullback.map (𝟙 V) (𝟙 V) (Sigma.desc fun _ : S ↦ 𝟙 V)
        (Sigma.desc fun _ : S ↦ 𝟙 V) (Sigma.ι (fun _ : S ↦ V) s) (Sigma.ι (fun _ : S ↦ V) s)
        (𝟙 V) e e :=
    pullback.hom_ext (by simp) (by simp)
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomp]

/-- The codiagonal of a coproduct of copies of a scheme is separated: its diagonal is an open
immersion whose range, the union of the equal-label components, is closed.
Source: Stacks Project, Tag 03YW. -/
lemma isSeparated_sigmaDesc_id (V : Scheme.{u}) (S : Type w) [Small.{u} S] :
    IsSeparated (Sigma.desc fun _ : S ↦ 𝟙 V : (∐ fun _ : S ↦ V) ⟶ V) := by
  set f : (∐ fun _ : S ↦ V) ⟶ V := Sigma.desc fun _ : S ↦ 𝟙 V
  have : Etale f := etale_sigmaDesc_id V S
  refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨s, a, ha⟩ := exists_sigmaι_eq (fun _ : S ↦ V) (pullback.fst f f z)
  obtain ⟨t, b, hb⟩ := exists_sigmaι_eq (fun _ : S ↦ V) (pullback.snd f f z)
  obtain rfl | hst := eq_or_ne s t
  · exact absurd (mem_range_diagonal_sigmaDesc_id V s z ⟨a, ha⟩ ⟨b, hb⟩) hz
  refine ⟨pullback.fst f f ⁻¹' Set.range (Sigma.ι (fun _ : S ↦ V) s) ∩
    pullback.snd f f ⁻¹' Set.range (Sigma.ι (fun _ : S ↦ V) t), ?_, ?_, ⟨a, ha⟩, ⟨b, hb⟩⟩
  · rintro _ ⟨h₁, h₂⟩ ⟨w, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.diagonal_fst] at h₁
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.diagonal_snd] at h₂
    exact (disjoint_opensRange_sigmaι (fun _ : S ↦ V) s t hst).le_bot ⟨h₁, h₂⟩
  · exact ((Sigma.ι (fun _ : S ↦ V) s).isOpenEmbedding.isOpen_range.preimage
      (pullback.fst f f).continuous).inter
      ((Sigma.ι (fun _ : S ↦ V) t).isOpenEmbedding.isOpen_range.preimage
        (pullback.snd f f).continuous)

/-- A quasi-compact scheme admitting an open immersion into a coproduct of affine schemes is
quasi-affine: its image meets only finitely many components, whose union is an affine open.
Source: Stacks Project, Tags 01P6 and 0AP6. -/
lemma isQuasiAffine_of_isOpenImmersion_sigma {σ : Type w} [Small.{u} σ] {g : σ → Scheme.{u}}
    [∀ i, IsAffine (g i)] {Z : Scheme.{u}} (φ : Z ⟶ ∐ g) [IsOpenImmersion φ] [CompactSpace Z] :
    Z.IsQuasiAffine := by
  classical
  obtain ⟨F, hF⟩ := (isCompact_range φ.continuous).elim_finite_subcover
    (fun i ↦ Set.range (Sigma.ι g i)) (fun i ↦ (Sigma.ι g i).isOpenEmbedding.isOpen_range)
    (fun x _ ↦ by
      obtain ⟨i, y, rfl⟩ := exists_sigmaι_eq g x
      exact Set.mem_iUnion.mpr ⟨i, y, rfl⟩)
  let A : (∐ g).Opens := ⨆ i ∈ (F : Set σ), (Sigma.ι g i).opensRange
  have : IsAffine A.toScheme := IsAffineOpen.biSup_of_disjoint F.finite_toSet
    (fun i _ ↦ isAffineOpen_opensRange _) (fun i _ j _ hij ↦ disjoint_opensRange_sigmaι g i j hij)
  have hle : Set.range φ ⊆ Set.range A.ι := by
    rw [Scheme.Opens.range_ι]
    simpa [A] using hF
  have : IsOpenImmersion (IsOpenImmersion.lift A.ι φ hle) := by
    have : IsOpenImmersion (IsOpenImmersion.lift A.ι φ hle ≫ A.ι) := by
      rw [IsOpenImmersion.lift_fac]
      infer_instance
    exact .of_comp _ A.ι
  exact Scheme.IsQuasiAffine.of_isImmersion (IsOpenImmersion.lift A.ι φ hle)

end AlgebraicGeometry
