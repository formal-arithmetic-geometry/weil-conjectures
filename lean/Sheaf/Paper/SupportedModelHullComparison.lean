/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.Paper.SupportedImageBoundedDerivedGeneration
public import Sheaf.Paper.SupportedModelHull
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.ConstructibleSheaf.OpenClosedStratification

/-! # Comparison of tree-path and chain supported hulls

Source: the support-chain comparison in the structural supported-generation plan,
blueprint latest, det-sf-comp-coherence-refinement.proof.md, paragraph (2).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem tree_qcqs {X : Scheme.{u}} (t : QcqsOpenClosedTree X) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  cases t <;> exact ⟨inferInstance, inferInstance⟩

private theorem path_to_chain {X W : Scheme.{u}} {t : QcqsOpenClosedTree X}
    (p : t.Path W) :
    ∃ q : ScalarModelSupportChain X W, Nonempty (p.extension Λ ≅ q.extension Λ) := by
  induction p with
  | root t => exact ⟨.nil _, ⟨Iso.refl _⟩⟩
  | openBranch j i h a b p ih =>
    obtain ⟨q, ⟨e⟩⟩ := ih
    exact ⟨.openStep j q, ⟨Functor.isoWhiskerRight e _⟩⟩
  | closedBranch j i h a b p ih =>
    obtain ⟨q, ⟨e⟩⟩ := ih
    have : CompactSpace _ := (tree_qcqs a).1
    have hc : IsCompact ((Set.range i.base)ᶜ) := by
      rw [← h]
      exact isCompact_range j.continuous
    exact ⟨.closedStep i hc q, ⟨Functor.isoWhiskerRight e _⟩⟩

private theorem chain_to_path {X W : Scheme.{u}}
    (q : ScalarModelSupportChain X W) [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (t : QcqsOpenClosedTree X) (p : t.Path W),
      Nonempty (q.extension Λ ≅ p.extension Λ) := by
  revert ‹CompactSpace X› ‹QuasiSeparatedSpace X›
  induction q with
  | nil X =>
    intro _ _
    exact ⟨.leaf X, .root _, ⟨Iso.refl _⟩⟩
  | @openStep X U W j hj hjqc q ih =>
    intro _ _
    have := hj
    have := hjqc
    have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
    have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated j
    obtain ⟨a, p, ⟨e⟩⟩ := ih
    let i := j.closedComplement
    have : IsClosedImmersion i := inferInstance
    let Z := (Scheme.IdealSheafData.vanishingIdeal
      ⟨(j.opensRange : Set X)ᶜ, j.opensRange.isOpen.isClosed_compl⟩).subscheme
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated i
    have h : Set.range j.base = (Set.range i.base)ᶜ := by
      simp only [i, Scheme.Hom.range_closedComplement, compl_compl]
    exact ⟨.split j i h a (.leaf _), .openBranch j i h a (.leaf _) p,
      ⟨Functor.isoWhiskerRight e _⟩⟩
  | @closedStep X Z W i hi hc q ih =>
    intro _ _
    have := hi
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated i
    obtain ⟨b, p, ⟨e⟩⟩ := ih
    let U := Scheme.openComplementOfIsClosedImmersion i
    have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hc
    have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
    have h : Set.range U.ι.base = (Set.range i.base)ᶜ := by
      simp [U, Scheme.openComplementOfIsClosedImmersion]
    exact ⟨.split U.ι i h (.leaf _) b, .closedBranch U.ι i h (.leaf _) b p,
      ⟨Functor.isoWhiskerRight e _⟩⟩

/-- The two admissibility predicates agree on qcqs schemes.

Source: support-chain comparison in the supported-generation plan.
(blueprint: lem-sfb-supported-model-hull-comparison).

Proof: turn each tree path into its chain. In the other direction, complete every
open or closed edge by a complementary leaf; quasi-compactness keeps all vertices
qcqs. The extension functors agree by induction. The remaining clauses are the
same, with strict lower bounds expressed either by IsStrictlyGE or termwise zero. -/
theorem supportedModelHullClass_iff (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) :
    IsSupportedModelHullClass Λ X P ↔
      CondensedRing.IsSupportedImageGenerationClass Λ X P := by
  constructor
  · rintro ⟨ht, hi, hr, hp, hf, hg⟩
    refine ⟨ht, hi, hr, hp, ?_, ?_⟩
    · intro t W p L hL
      obtain ⟨q, ⟨e⟩⟩ := path_to_chain Λ p
      have := hi
      exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
        (e.app L)).symm (hg W q L hL)
    · intro I _ _ D a c hc ha hD
      exact hf I D a (fun i n hn ↦ (CochainComplex.isStrictlyGE_iff _ _).mp (ha i) n hn) hD c hc
  · rintro ⟨ht, hi, hr, hp, hg, hf⟩
    refine ⟨ht, hi, hr, hp, ?_, ?_⟩
    · intro I _ _ D a ha hD c hc
      exact hf I D a c hc
        (fun i ↦ (CochainComplex.isStrictlyGE_iff _ _).mpr (ha i)) hD
    · intro W q L hL
      obtain ⟨t, p, ⟨e⟩⟩ := chain_to_path Λ q
      have := hi
      exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
        (e.app L)).symm (hg t W p L hL)

/-- Tree paths and finite support chains define the same supported derived hull.

Source: support-chain comparison in the supported-generation plan.
(blueprint: lem-sfb-supported-model-hull-comparison).

Proof: evaluate each hull membership assertion on the same property P and use
supportedModelHullClass_iff to translate its admissibility. No choice of generators
or change of support extension is involved. -/
theorem supportedModelHull_iff (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    supportedModelHull Λ X K ↔ CondensedRing.supportedImageGenerationHull Λ X K := by
  constructor
  · intro h P hP
    exact h P ((supportedModelHullClass_iff Λ X P).mpr hP)
  · intro h P hP
    exact h P ((supportedModelHullClass_iff Λ X P).mp hP)

end AlgebraicGeometry.ProEtale
