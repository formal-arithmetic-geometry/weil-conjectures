/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fpqc cover from a field extension

## References

* Stacks Project, Tags 022B, 03L7 and 00HB
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a field extension `K/k`, the structure map `Spec K ⟶ Spec k` is flat, surjective, and
quasi-compact, and its singleton presieve is an fpqc covering (Stacks, Tags 022B, 03L7, 00HB). -/
theorem fpqcCover_specMap_algebraMap_of_field
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∈
        Scheme.fpqcPrecoverage (Spec (.of k)) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

end AlgebraicGeometry
