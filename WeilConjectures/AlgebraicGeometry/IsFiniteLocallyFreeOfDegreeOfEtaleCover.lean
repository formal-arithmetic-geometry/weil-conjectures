/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import WeilConjectures.AlgebraicGeometry.FlatOfFpqcCover
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent

/-!
# Descent of finite local freeness of fixed degree along an étale covering

## References

* Stacks Project, Descent, Lemma 02VO, and Topologies, Lemma 022C.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- Finite local freeness of degree `d` descends along a jointly surjective étale family.
(Stacks, Tags 02VO, 022C) -/
theorem isFiniteLocallyFreeOfDegree_of_etale_cover
    {Y T : Scheme.{u}} (h : Y ⟶ T) (d : ℕ) {I : Type w}
    (T' : I → Scheme.{u}) (φ : ∀ i : I, T' i ⟶ T)
    (hφ : ∀ i : I, Etale (φ i))
    (hcover : ∀ t : T, ∃ (i : I) (t' : T' i), φ i t' = t)
    (hdegree : ∀ i : I, (pullback.snd h (φ i)).IsFiniteLocallyFreeOfDegree d) :
    h.IsFiniteLocallyFreeOfDegree d := by
  let (i : I) : Etale (φ i) := hφ i
  let (i : I) : (pullback.snd h (φ i)).IsFiniteLocallyFreeOfDegree d := hdegree i
  have hfpqc : Presieve.ofArrows T' φ ∈ Scheme.fpqcPrecoverage T := by
    apply Scheme.fppfPrecoverage_le_fpqcPrecoverage
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hcover, fun i ↦ ⟨inferInstance, inferInstance⟩⟩
  let : IsFinite h := isFinite_of_fpqc_cover h T' φ hfpqc (fun i ↦ inferInstance)
  let : Flat h := flat_of_fpqc_cover h T' φ hfpqc (fun i ↦ inferInstance)
  let : LocallyOfFinitePresentation h :=
    locallyOfFinitePresentation_of_fpqc_cover h T' φ hfpqc (fun i ↦ inferInstance)
  refine { fiberDegree_eq := ?_ }
  intro t
  obtain ⟨i, t', rfl⟩ := hcover t
  rw [← h.fiberDegree_of_isPullback (IsPullback.of_hasPullback h (φ i)) t']
  exact IsFiniteLocallyFreeOfDegree.fiberDegree_eq t'

end AlgebraicGeometry.Scheme.Hom
