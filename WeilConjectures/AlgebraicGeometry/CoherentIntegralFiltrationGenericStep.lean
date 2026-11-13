/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.CoherentGenericPointIdealInclusion
import WeilConjectures.AlgebraicGeometry.CoherentIdealSumCokernelReduction
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationIdealSum
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # The generic-point step of the coherent integral-ideal filtration

Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The generic-residue-field case of support induction: the coherent cokernel of
the generic ideal inclusion has smaller support, and its filtration can be appended.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, proof, final paragraph,
using Lemma 01YE (coherent_generic_point_ideal_inclusion). -/
theorem coherentIntegralFiltration_generic_step
    (X : Scheme.{u}) [IsNoetherian X]
    (T : TopologicalSpace.Closeds X) (ξ : X)
    (hξ : IsGenericPoint ξ (T : Set X))
    (hsmaller : ∀ (G : X.Modules), RingedSpace.IsCoherent X.toRingedSpace G →
      {x : X | ¬ Subsingleton (G.presheaf.stalk x)} ⊂ (T : Set X) →
      HasCoherentIntegralFiltration G)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hSupp : {x : X | ¬ Subsingleton (F.presheaf.stalk x)} = (T : Set X))
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj F, a • m = 0) :
    HasCoherentIntegralFiltration F := by
  classical
  let J := Scheme.IdealSheafData.vanishingIdeal T
  let Z := J.subscheme
  let i : Z ⟶ X := J.subschemeι
  have hrange : Set.range i.base = (T : Set X) := by
    change Set.range J.subschemeι = (T : Set X)
    simp [J]
  let e : Z ≃ₜ (T : Set X) :=
    i.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have : IrreducibleSpace (T : Set X) := Subtype.irreducibleSpace hξ.isIrreducible
  have : IrreducibleSpace Z := e.irreducibleSpace_iff.mpr inferInstance
  have : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  have hpoint : i (genericPoint Z) = ξ := by
    have h := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, hrange, T.isClosed.closure_eq] at h
    exact h.eq hξ
  have hkill' : ∀ a ∈ IsLocalRing.maximalIdeal
      (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).obj F, a • m = 0 := by
    rw [hpoint]
    exact hkill
  obtain ⟨r, I, hI, α, hα, W, hW, hαW⟩ :=
    coherent_generic_point_ideal_inclusion i F hF hkill'
  have : Mono α := hα
  have hx : ¬ Subsingleton (F.presheaf.stalk (i.base (genericPoint Z))) := by
    have hx' : ξ ∈ {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
      rw [hSupp]
      exact hξ.mem
    rw [hpoint]
    exact hx'
  obtain ⟨hne, hA, hQ, hQsub⟩ :=
    coherent_ideal_sum_cokernel_reduction i r I hI F hF α
      (i.base (genericPoint Z)) hx W hW hαW
  have hQfil : HasCoherentIntegralFiltration (cokernel α) := by
    apply hsmaller (cokernel α) hQ
    simpa only [hSupp] using hQsub
  have hS : (ShortComplex.mk α (cokernel.π α) (cokernel.condition α)).ShortExact := by
    exact { exact := ShortComplex.exact_cokernel α }
  exact coherentIntegralFiltration_of_shortExact X
    (ShortComplex.mk α (cokernel.π α) (cokernel.condition α)) hS hA hF hQ
    (coherentIntegralFiltration_ideal_sum i r I hne hI) hQfil

end AlgebraicGeometry.Scheme.Modules
