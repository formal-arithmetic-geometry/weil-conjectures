/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exactness in functor categories is detected pointwise

## Main statements

- `CategoryTheory.ShortComplex.shortExact_of_evaluation`: a short complex of functors which is
  short exact after evaluation at every object is short exact.
- `HomologicalComplex.acyclic_iff_evaluation`: a complex of functors is acyclic if and only if
  it is acyclic after evaluation at every object.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

variable {T V : Type*} [Category* T] [Category* V] [Abelian V]

namespace CategoryTheory.ShortComplex

/-- A short complex of functors is short exact as soon as it is short exact after evaluation
at every object. -/
lemma shortExact_of_evaluation {S : ShortComplex (T ⥤ V)}
    (h : ∀ t : T, (S.map ((evaluation T V).obj t)).ShortExact) : S.ShortExact := by
  have (t : T) : Mono (S.f.app t) := (h t).mono_f
  have (t : T) : Epi (S.g.app t) := (h t).epi_g
  have := NatTrans.mono_of_mono_app S.f
  have := NatTrans.epi_of_epi_app S.g
  refine ⟨?_⟩
  rw [exact_iff_isZero_homology]
  exact Functor.isZero _ fun t ↦ ((exact_iff_isZero_homology _).1 (h t).exact).of_iso
    (S.mapHomologyIso ((evaluation T V).obj t)).symm

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι}

/-- A complex of functors is acyclic if and only if it is acyclic after evaluation at every
object. -/
lemma acyclic_iff_evaluation (K : HomologicalComplex (T ⥤ V) c) :
    K.Acyclic ↔ ∀ t : T, (((evaluation T V).obj t).mapHomologicalComplex c |>.obj K).Acyclic := by
  have h₀ (t : T) (i : ι) : (((evaluation T V).obj t).mapHomologicalComplex c |>.obj
      (0 : HomologicalComplex (T ⥤ V) c)).ExactAt i :=
    ExactAt.of_isZero (((evaluation T V).obj t).map_isZero
      ((eval _ c i).map_isZero (Limits.isZero_zero _)))
  have h₁ (i : ι) : (0 : HomologicalComplex (T ⥤ V) c).ExactAt i :=
    ExactAt.of_isZero ((eval _ c i).map_isZero (Limits.isZero_zero _))
  have := quasiIso_iff_evaluation (0 : K ⟶ 0)
  rw [quasiIso_iff] at this
  simp only [quasiIso_iff] at this
  exact (forall_congr' fun i ↦ quasiIsoAt_iff_exactAt' _ _ (h₁ i)).symm.trans (this.trans
    (forall_congr' fun t ↦ forall_congr' fun i ↦ quasiIsoAt_iff_exactAt' _ _ (h₀ t i)))

end HomologicalComplex
