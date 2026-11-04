/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Left exact functors and quasi-isomorphisms in degree zero

A left exact functor preserves quasi-isomorphisms in degree `0` between cochain complexes
which vanish in degree `-1`.
-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- A left exact functor preserves quasi-isomorphisms in degree `0` between cochain complexes
which vanish in degree `-1`: in degree `0` the homology of such a complex is the kernel of the
differential, which a left exact functor preserves. -/
lemma quasiIsoAt_map_zero_of_preservesFiniteLimits (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (hK : IsZero (K.X (-1))) (hL : IsZero (L.X (-1))) [QuasiIsoAt φ 0] :
    QuasiIsoAt ((F.mapHomologicalComplex _).map φ) 0 := by
  have hprev : (ComplexShape.up ℤ).prev 0 = -1 := by simp
  have : F.PreservesLeftHomologyOf (K.sc 0) :=
    F.preservesLeftHomology_of_zero_f _ ((hprev ▸ hK : IsZero (K.X _)).eq_of_src _ _)
  have : F.PreservesLeftHomologyOf (L.sc 0) :=
    F.preservesLeftHomology_of_zero_f _ ((hprev ▸ hL : IsZero (L.X _)).eq_of_src _ _)
  have hφ : QuasiIsoAt φ 0 := inferInstance
  rw [quasiIsoAt_iff] at hφ ⊢
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((HomologicalComplex.shortComplexFunctor C _ 0).map φ)

end CochainComplex
