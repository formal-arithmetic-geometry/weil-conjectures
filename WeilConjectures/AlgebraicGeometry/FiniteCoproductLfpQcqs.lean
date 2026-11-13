/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Quasi-compactness, quasi-separatedness and local finite presentation of finite coproducts

## References

* Stacks Project, Tags 01KO and 01TQ.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite coproduct of schemes preserves quasi-compactness and quasi-separatedness, and
its induced morphism is locally of finite presentation when each component morphism is.
(Stacks, Tags 01KO and 01TQ.) -/
theorem finite_coproduct_lfp_qcqs {A : Type v} [Finite A] (V : A → Scheme.{u})
    (S : Scheme.{u}) (g : ∀ a : A, V a ⟶ S) :
    ((∀ a : A, CompactSpace (V a)) → CompactSpace ↥(∐ V)) ∧
    ((∀ a : A, QuasiSeparatedSpace (V a)) → QuasiSeparatedSpace ↥(∐ V)) ∧
    ((∀ a : A, LocallyOfFinitePresentation (g a)) →
      LocallyOfFinitePresentation (Sigma.desc g)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hV
    let 𝒰 := sigmaOpenCover V
    let : Finite 𝒰.I₀ := by
      change Finite A
      infer_instance
    let : ∀ i, CompactSpace (𝒰.X i) := by
      intro i
      exact hV i
    exact 𝒰.compactSpace
  · intro hV
    let e := equivShrink.{u} A
    have : Finite (Shrink.{u} A) := Finite.of_equiv A e
    let V' : Shrink.{u} A → Scheme.{u} := fun a ↦ V (e.symm a)
    have : ∀ a, QuasiSeparatedSpace (V' a) := fun a ↦ hV (e.symm a)
    apply (quasiSeparatedSpace_congr (Sigma.reindex e.symm V).hom.homeomorph).mp
    apply (quasiSeparatedSpace_congr (sigmaMk V')).mp
    refine ⟨?_⟩
    intro U W hUo hUc hWo hWc
    have hcompact : ∀ a : Shrink.{u} A,
        IsCompact (Sigma.mk a '' (Sigma.mk a ⁻¹' (U ∩ W))) := by
      intro a
      apply IsCompact.image _ continuous_sigmaMk
      rw [Set.preimage_inter]
      exact (Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hUc).inter_of_isOpen
        (Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hWc)
        (hUo.preimage continuous_sigmaMk) (hWo.preimage continuous_sigmaMk)
    rw [← Set.iUnion_image_preimage_sigma_mk_eq_self (U ∩ W)]
    exact isCompact_iUnion hcompact
  · intro hg
    exact IsZariskiLocalAtSource.sigmaDesc hg

end AlgebraicGeometry
