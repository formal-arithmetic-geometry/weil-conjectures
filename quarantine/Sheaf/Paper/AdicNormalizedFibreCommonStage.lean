/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.Paper.AdicNormalizedFibreCommonStageData
import Sheaf.Paper.AdicCommonStageHeartExactness
import Sheaf.Paper.AdicCommonStageFibreTransport
import Sheaf.Paper.AdicCommonStageFibreZeroMap
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Descent and detection of normalized common-stage fibres -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

section JointDetection

variable {I C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (T : I → C ⥤ D) [∀ i, (T i).Additive]
    (hz : ∀ {F G : C} (f : F ⟶ G), (∀ i, (T i).map f = 0) → f = 0)

include hz in
private theorem joint_mono {F G : C} (f : F ⟶ G)
    (hf : ∀ i, Mono ((T i).map f)) : Mono f := by
  apply Abelian.mono_of_kernel_ι_eq_zero
  apply hz (kernel.ι f)
  intro i
  have := hf i
  apply (cancel_mono ((T i).map f)).1
  rw [← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp]

include hz in
private theorem joint_epi {F G : C} (f : F ⟶ G)
    (hf : ∀ i, Epi ((T i).map f)) : Epi f := by
  apply Abelian.epi_of_cokernel_π_eq_zero
  apply hz (cokernel.π f)
  intro i
  have := hf i
  apply (cancel_epi ((T i).map f)).1
  rw [← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero]

include hz in
private theorem joint_exact (S : ShortComplex C)
    (hS : ∀ i, (S.map (T i)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
  apply hz (kernel.ι S.g ≫ cokernel.π S.f)
  intro i
  have ht := hS i
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at ht
  change kernel.ι ((T i).map S.g) ≫ cokernel.π ((T i).map S.f) = 0 at ht
  obtain ⟨a, ha⟩ := kernel.lift' ((T i).map S.g) ((T i).map (kernel.ι S.g))
    (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])
  obtain ⟨b, hb⟩ := cokernel.desc' ((T i).map S.f) ((T i).map (cokernel.π S.f))
    (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero])
  rw [Functor.map_comp, ← ha, ← hb, Category.assoc,
    ← Category.assoc (kernel.ι _) _ b, ht, zero_comp, comp_zero]

end JointDetection

/-- Normalized finite-stage fibres descend to exact common-heart fibres with
joint detection, finite-stage exact representatives and normalized pullback comparisons.
Source: BS 6.8.14--6.8.15
(blueprint: lem-per-adic-normalized-fibre-common-stage).

Proof: take the finite-stage heart exactness data and the normalized transport family.
Joint zero-map detection follows by representing an arrow at one finite heart stage.
It detects a zero object by testing its identity. If every fibre of an arrow is monic,
its kernel inclusion has zero image at every fibre by cancellation, so that inclusion
is zero and the arrow is monic. The cokernel projection gives the dual epicity test;
together these detect isomorphisms. A short complex is exact precisely when its kernel
inclusion followed by its cokernel projection is zero. Every functor factors the image
of this composite through the corresponding kernel-to-cokernel composite of its image
complex. Fibrewise exactness kills the latter, so joint zero-map detection kills the
former. Combining this with the mono and epi tests detects short exactness. The forward
tests follow from additivity, functoriality and the exactness already in CommonPoint.
The scalar and pullback normalization equations and their coherence are retained from
the transport family. No arbitrary choice of a data witness is made in a definition.
-/
theorem adic_normalized_fibre_common_stage
    (ω : Fibres (k := k) l R) (α : NormalizedPullback l R ω)
    (β : NormalizedScalar l R ω α) :
    Nonempty (CommonStageFibreDescent.{u, v, w} l R Ω ω α β) := by
  obtain ⟨h⟩ := common_stage_heart_exactness.{u, v, w} l Ω (k := k)
  obtain ⟨V⟩ := common_stage_fibre_transport l R Ω ω α β h
  have hz := common_stage_fibre_zero_map l R Ω ω V.point h
  let T (X : FiniteTypeBase k) (p : NormalizedFibre.GeometricPoint X.scheme) :=
    (V.point X p.field p.map).functor
  have hz' (X : FiniteTypeBase k)
      {F G : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory} (f : F ⟶ G)
      (hf : ∀ p, (T X p).map f = 0) : f = 0 := by
    apply hz X F G f
    intro κ _ _ x
    exact hf ⟨κ, x⟩
  refine ⟨{
    toCommonStageFibreTransport := V
    heart_exactness := h
    detects_zero := ?_
    detects_iso := ?_
    detects_zero_map := ?_
    detects_short_exact := ?_
  }⟩
  · intro X F
    constructor
    · intro hF
      apply (IsZero.iff_id_eq_zero F).2
      apply hz X F F (𝟙 F)
      intro κ _ _ x
      rw [(V.point X κ x).functor.map_id]
      exact (hF κ x).eq_of_src _ _
    · intro hF κ _ _ x
      exact (V.point X κ x).functor.map_isZero hF
  · intro X F G f
    constructor
    · intro hf
      have : Mono f := joint_mono (T X) (hz' X) f (fun p ↦ by
        have := hf p.field p.map
        infer_instance)
      have : Epi f := joint_epi (T X) (hz' X) f (fun p ↦ by
        have := hf p.field p.map
        infer_instance)
      exact isIso_of_mono_of_epi f
    · intro hf κ _ _ x
      infer_instance
  · intro X F G f
    constructor
    · exact hz X F G f
    · rintro rfl κ _ _ x
      exact (V.point X κ x).functor.map_zero _ _
  · intro X S
    constructor
    · intro hS κ _ _ x
      exact (V.point X κ x).exact S hS
    · intro hS
      exact ShortComplex.ShortExact.mk'
        (joint_exact (T X) (hz' X) S (fun p ↦ (hS p.field p.map).exact))
        (joint_mono (T X) (hz' X) S.f (fun p ↦ (hS p.field p.map).mono_f))
        (joint_epi (T X) (hz' X) S.g (fun p ↦ (hS p.field p.map).epi_g))

end AlgebraicGeometry.Scheme.AdicFibreComparison
