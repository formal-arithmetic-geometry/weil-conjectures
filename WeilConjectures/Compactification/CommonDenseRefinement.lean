/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Compactification.BoundaryRefinement

/-!
# The closure of the diagonal is a common dense refinement
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Compactification

private lemma infFst_preimage {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    (c d : Compactification f) :
    (infFst c d).hom ⁻¹ᵁ c.i.opensRange = (inf c d).i.opensRange := by
  apply SetLike.coe_injective
  exact (range_snd_of_isPullback (isPullback_infFst c d).flip).symm

private lemma infSnd_preimage {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    (c d : Compactification f) :
    (infSnd c d).hom ⁻¹ᵁ d.i.opensRange = (inf c d).i.opensRange := by
  apply SetLike.coe_injective
  exact (range_snd_of_isPullback (isPullback_infSnd c d).flip).symm

/-- For two compactifications of a separated finite-type morphism over a qcqs scheme,
the scheme-theoretic image of the diagonal graph is a dense compactification refining both.
Stacks Project, Tags 01W3, 01W4, 01W5, 01JY, 01QR, 01RG and 01R7. -/
theorem exists_common_dense_refinement {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c₁ c₂ : Compactification f) :
    IsClosedImmersion (graph c₁ c₂).imageι ∧
      IsOpenImmersion (inf c₁ c₂).i ∧ QuasiCompact (inf c₁ c₂).i ∧
      IsSchemeTheoreticallyDominant (inf c₁ c₂).i ∧
      IsProper (inf c₁ c₂).g ∧
      (graph c₁ c₂).toImage ≫ (graph c₁ c₂).imageι = graph c₁ c₂ ∧
      (inf c₁ c₂).Z = (graph c₁ c₂).image ∧
      (inf c₁ c₂).i = (graph c₁ c₂).toImage ∧
      (inf c₁ c₂).g =
        (graph c₁ c₂).imageι ≫ pullback.fst c₁.g c₂.g ≫ c₁.g ∧
      (infFst c₁ c₂).hom =
        (graph c₁ c₂).imageι ≫ pullback.fst c₁.g c₂.g ∧
      (infSnd c₁ c₂).hom =
        (graph c₁ c₂).imageι ≫ pullback.snd c₁.g c₂.g ∧
      Compactification.boundaryRefinementProperty f
          (ObjectProperty.homMk
            (X := ⟨inf c₁ c₂, (inf c₁ c₂).quasiCompact_openImmersion inferInstance⟩)
            (Y := ⟨c₁, c₁.quasiCompact_openImmersion inferInstance⟩)
            ⟨(infFst c₁ c₂).hom, (infFst c₁ c₂).i_hom, (infFst c₁ c₂).hom_g⟩) ∧
      Compactification.boundaryRefinementProperty f
          (ObjectProperty.homMk
            (X := ⟨inf c₁ c₂, (inf c₁ c₂).quasiCompact_openImmersion inferInstance⟩)
            (Y := ⟨c₂, c₂.quasiCompact_openImmersion inferInstance⟩)
            ⟨(infSnd c₁ c₂).hom, (infSnd c₁ c₂).i_hom, (infSnd c₁ c₂).hom_g⟩) ∧
      (∀ (I : Type v) [Finite I] [Nonempty I]
        (d : I → Compactification f),
        ∃ (e : Compactification f),
          IsSchemeTheoreticallyDominant e.i ∧
          ∀ i : I, ∃ (h : e.Z ⟶ (d i).Z),
            ∃ (hj : e.i ≫ h = (d i).i),
              ∃ (hS : h ≫ (d i).g = e.g),
                Compactification.boundaryRefinementProperty f
                  (ObjectProperty.homMk
                    (X := ⟨e, e.quasiCompact_openImmersion inferInstance⟩)
                    (Y := ⟨d i, (d i).quasiCompact_openImmersion inferInstance⟩)
                    ⟨h, hj, hS⟩)) := by
  classical
  have hqc (c : Compactification f) : QuasiCompact c.i :=
    c.quasiCompact_openImmersion inferInstance
  refine ⟨inferInstance, inferInstance, hqc _,
    isSchemeTheoreticallyDominant_inf_i c₁ c₂, inferInstance,
    Scheme.Hom.toImage_imageι _, inf_Z _ _, inf_i _ _, ?_,
    infFst_hom _ _, infSnd_hom _ _, ?_, ?_, ?_⟩
  · exact Category.assoc _ _ _
  · exact infFst_preimage c₁ c₂
  · exact infSnd_preimage c₁ c₂
  · intro I _ _ d
    let := Fintype.ofFinite I
    have hfinite (t : Finset I) :
        ∃ e : Compactification f, IsSchemeTheoreticallyDominant e.i ∧
          ∀ i ∈ t, ∃ r : e.Refinement (d i),
            r.hom ⁻¹ᵁ (d i).i.opensRange = e.i.opensRange := by
      induction t using Finset.induction_on with
      | empty =>
          exact ⟨inf c₁ c₁, isSchemeTheoreticallyDominant_inf_i c₁ c₁,
            fun _ hi ↦ False.elim (Finset.notMem_empty _ hi)⟩
      | @insert i t hi ih =>
          obtain ⟨e, he, ht⟩ := ih
          refine ⟨inf e (d i), isSchemeTheoreticallyDominant_inf_i e (d i), ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact ⟨infSnd e (d j), infSnd_preimage e (d j)⟩
          · obtain ⟨r, hr⟩ := ht j hj
            refine ⟨(infFst e (d i)).comp r, ?_⟩
            change ((infFst e (d i)).hom ≫ r.hom) ⁻¹ᵁ _ = _
            rw [Scheme.Hom.comp_preimage, hr, infFst_preimage]
    obtain ⟨e, he, ht⟩ := hfinite Finset.univ
    refine ⟨e, he, ?_⟩
    intro i
    obtain ⟨r, hr⟩ := ht i (Finset.mem_univ i)
    exact ⟨r.hom, r.i_hom, r.hom_g, hr⟩

end AlgebraicGeometry.Compactification
