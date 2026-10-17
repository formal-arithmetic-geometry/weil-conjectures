/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CofilteredLimitOverDescent
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.ProEtale.Coherent.Etale

/-!
# Auxiliary results for the descent of finite split étale hypercovers

* finite coproducts of quasi-compact quasi-separated schemes are quasi-compact and
  quasi-separated;
* the terms of a truncated finite split étale hypercover over a qcqs scheme are qcqs étale;
* transport of descended morphisms along further transition maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

/-- A finite disjoint union of quasi-separated spaces is quasi-separated. -/
lemma quasiSeparatedSpace_sigma {ι : Type*} [Finite ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, QuasiSeparatedSpace (X i)] :
    QuasiSeparatedSpace (Σ i, X i) := by
  refine ⟨fun U V hUo hUc hVo hVc ↦ ?_⟩
  have hU : ∀ i, IsCompact (Sigma.mk i ⁻¹' U) := fun i ↦
    Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hUc
  have hV : ∀ i, IsCompact (Sigma.mk i ⁻¹' V) := fun i ↦
    Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hVc
  have : U ∩ V = ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' U ∩ Sigma.mk i ⁻¹' V) := by
    ext ⟨i, x⟩
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨hx, hx'⟩
      exact ⟨i, x, ⟨hx, hx'⟩, rfl⟩
    · rintro ⟨j, y, ⟨hy, hy'⟩, h⟩
      rw [← h]
      exact ⟨hy, hy'⟩
  rw [this]
  exact isCompact_iUnion fun i ↦ (QuasiSeparatedSpace.inter_isCompact _ _
    (hUo.preimage continuous_sigmaMk) (hU i) (hVo.preimage continuous_sigmaMk) (hV i)).image
    continuous_sigmaMk

namespace AlgebraicGeometry

/-- The apex of a finite coproduct of quasi-compact quasi-separated schemes is quasi-compact and
quasi-separated. -/
lemma Scheme.compactSpace_quasiSeparatedSpace_of_isColimit {ι : Type*} [Finite ι]
    {Y : ι → Scheme.{u}} {Z : Scheme.{u}} (f : ∀ k, Y k ⟶ Z) (hs : IsColimit (Cofan.mk Z f))
    [∀ k, CompactSpace (Y k)] [∀ k, QuasiSeparatedSpace (Y k)] :
    CompactSpace Z ∧ QuasiSeparatedSpace Z := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  let ε : ULift.{u} (Fin n) ≃ ι := Equiv.ulift.trans e.symm
  let Y' : ULift.{u} (Fin n) → Scheme.{u} := Y ∘ ε
  let iso : Z ≅ ∐ Y' :=
    hs.coconePointUniqueUpToIso (colimit.isColimit _) ≪≫ (Sigma.reindex ε Y).symm
  let h : (Σ k, Y' k) ≃ₜ Z := (sigmaMk Y').trans iso.inv.homeomorph
  have : ∀ k, CompactSpace (Y' k) := fun k ↦ inferInstanceAs (CompactSpace (Y (ε k)))
  have : ∀ k, QuasiSeparatedSpace (Y' k) := fun k ↦
    inferInstanceAs (QuasiSeparatedSpace (Y (ε k)))
  exact ⟨h.compactSpace, (quasiSeparatedSpace_congr h).mp quasiSeparatedSpace_sigma⟩

/-- The apex of a finite coproduct in `X.Etale` of quasi-compact quasi-separated schemes is
quasi-compact and quasi-separated. -/
lemma Scheme.Etale.compactSpace_quasiSeparatedSpace_of_isColimit {X : Scheme.{u}} {ι : Type*}
    [Finite ι] {Y : ι → X.Etale} {Z : X.Etale} (f : ∀ k, Y k ⟶ Z)
    (hs : IsColimit (Cofan.mk Z f))
    (hY : ∀ k, CompactSpace (Y k).left ∧ QuasiSeparatedSpace (Y k).left) :
    CompactSpace Z.left ∧ QuasiSeparatedSpace Z.left := by
  have hs' := isColimitCofanMkObjOfIsColimit (Scheme.Etale.forget X ⋙ Over.forget X) Y Z f hs
  have : ∀ k, CompactSpace ((Scheme.Etale.forget X ⋙ Over.forget X).obj (Y k)) :=
    fun k ↦ (hY k).1
  have : ∀ k, QuasiSeparatedSpace ((Scheme.Etale.forget X ⋙ Over.forget X).obj (Y k)) :=
    fun k ↦ (hY k).2
  exact Scheme.compactSpace_quasiSeparatedSpace_of_isColimit _ hs'

/-- An étale scheme over a quasi-compact quasi-separated base whose underlying space is
quasi-compact and quasi-separated is qcqs étale. -/
lemma isQcqsEtale_of_compactSpace {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (Z : X.Etale) [CompactSpace Z.left] [QuasiSeparatedSpace Z.left] :
    IsQcqsEtale ((Scheme.Etale.forget X).obj Z) :=
  ⟨Z.prop, inferInstanceAs (LocallyOfFinitePresentation Z.hom),
    inferInstanceAs (QuasiCompact Z.hom), inferInstanceAs (QuasiSeparated Z.hom)⟩

end AlgebraicGeometry
