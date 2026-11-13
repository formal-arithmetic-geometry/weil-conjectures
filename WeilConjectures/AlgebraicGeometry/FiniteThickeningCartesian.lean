/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeThickening
import WeilConjectures.AlgebraicGeometry.ThickeningIntegral

/-!
# Finiteness across a cartesian finite order thickening

## References

* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finiteness is equivalent before and after base change along a finite order thickening.
(Stacks, Tag 09ZW, part (8).) -/
theorem isFinite_iff_of_finiteOrderThickening {S S' X' : Scheme.{u}}
    (i : S ⟶ S') (f' : X' ⟶ S') (hi : IsFiniteOrderThickening i) :
    IsFinite (pullback.snd f' i) ↔ IsFinite f' := by
  obtain ⟨n, hclosed, hnil⟩ := hi
  let : IsClosedImmersion i := hclosed
  have hsupport : i.ker.support = ⊤ := by
    rw [← Scheme.IdealSheafData.support_pow_succ i.ker n, hnil]
    exact Scheme.IdealSheafData.support_bot
  have hsurj : Function.Surjective i := by
    apply Set.range_eq_univ.mp
    rw [← i.isClosedEmbedding.isClosed_range.closure_eq, ← i.support_ker, hsupport]
    rfl
  let : Surjective i := ⟨hsurj⟩
  constructor
  · intro hf
    let : IsFinite (pullback.snd f' i) := hf
    have hint : IsIntegralHom f' :=
      (isIntegralHom_iff_of_thickenings i (pullback.fst f' i) f'
        (pullback.snd f' i) ⟨hclosed, inferInstance⟩
        ⟨inferInstance, inferInstance⟩ pullback.condition).mp inferInstance
    have hlft : LocallyOfFiniteType (pullback.fst i f') := by
      rw [← pullbackSymmetry_hom_comp_snd i f']
      infer_instance
    exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f').mpr
      ⟨hint, (locallyOfFiniteType_iff_of_finiteOrderThickening i f' ⟨n, hclosed, hnil⟩).mp hlft⟩
  · intro hf
    let : IsFinite f' := hf
    infer_instance

end AlgebraicGeometry
