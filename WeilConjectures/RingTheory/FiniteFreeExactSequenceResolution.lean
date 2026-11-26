/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Finite exact sequences as bounded projective resolutions

An exact sequence `0 → F_d → ⋯ → F_0 → M → 0` of modules with `F_i` finite free is packaged as a
bounded finite free projective resolution of `M`.

## Implementation details

The object of index `d + 1 - i` is placed in chain degree `i` for `i ≤ d`, with zero modules in
larger degrees; the differentials are the arrows of the sequence and the augmentation is the
arrow of index `d + 1`.

## References

* [Stacks, Tag 0CXF]
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace ModuleCat

/-- An exact sequence with zero endpoints and finite free resolution terms yields a
bounded finite free projective resolution of its penultimate object. -/
theorem exists_bounded_finite_free_resolution_of_exact_sequence
    {R : Type u} [CommRing R] (d : ℕ)
    (S : ComposableArrows (ModuleCat.{max u v} R) (d + 3))
    (hS : S.Exact) (hzero : IsZero (S.obj' 0)) (hlast : IsZero (S.obj' (d + 3)))
    (hfree : ∀ (i : ℕ) (hi : i ≤ d),
      Module.Finite R (S.obj' (i + 1) (by omega)) ∧
        Module.Free R (S.obj' (i + 1) (by omega))) :
    ∃ P : ProjectiveResolution (S.obj' (d + 2)),
      (∀ i : ℕ, d < i → IsZero (P.complex.X i)) ∧
      (∀ i : ℕ, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) := by
  classical
  let X (i : ℕ) : ModuleCat.{max u v} R := S.obj' (d + 1 - i) (by omega)
  let δ (i : ℕ) : X (i + 1) ⟶ X i :=
    S.map' (d + 1 - (i + 1)) (d + 1 - i) (by omega) (by omega)
  have hz (i : ℕ) (hi : d < i) : IsZero (X i) := by
    have he : d + 1 - i = 0 := by omega
    simpa only [X, he] using hzero
  have sq (i : ℕ) : δ (i + 1) ≫ δ i = 0 := by
    by_cases hi : i < d
    · exact hS.toIsComplex.zero' (d + 1 - (i + 1 + 1))
        (d + 1 - (i + 1)) (d + 1 - i) (by omega) (by omega) (by omega)
    · exact (hz (i + 2) (by omega)).eq_of_src _ _
  let K := ChainComplex.of X δ sq
  have hfin (i : ℕ) : Module.Finite R (X i) ∧ Module.Free R (X i) := by
    by_cases hi : i ≤ d
    · have he : d + 1 - i = (d - i) + 1 := by omega
      have heX : X i = S.obj' ((d - i) + 1) (by omega) := by
        dsimp only [X, ComposableArrows.obj']
        congr 1
        exact Fin.ext he
      rw [heX]
      exact hfree (d - i) (by omega)
    · let := ModuleCat.subsingleton_of_isZero (hz i (by omega))
      exact ⟨inferInstance, inferInstance⟩
  have kd (i : ℕ) : K.d (i + 1) i = δ i := ChainComplex.of_d X δ i
  have hex (i : ℕ) : K.ExactAt (i + 1) := by
    rw [HomologicalComplex.exactAt_iff' K (i + 2) (i + 1) i (by simp) (by simp)]
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', kd]
    change (ShortComplex.mk (δ (i + 1)) (δ i) (sq i)).Exact
    by_cases hi : i < d
    · exact hS.exact' (d + 1 - (i + 1 + 1)) (d + 1 - (i + 1))
        (d + 1 - i) (by omega) (by omega) (by omega)
    · exact ShortComplex.exact_of_isZero_X₂ _ (hz (i + 1) (by omega))
  let ε : K.X 0 ⟶ S.obj' (d + 2) := S.map' (d + 1) (d + 2)
  have hw : K.d 1 0 ≫ ε = 0 := by
    change S.map' (d + 1 - 1) (d + 1 - 0) ≫ S.map' (d + 1) (d + 2) = 0
    simpa only [Nat.add_sub_cancel, Nat.sub_zero] using hS.toIsComplex.zero d
  have hex₀ : (ShortComplex.mk (K.d 1 0) ε hw).Exact := by
    simp only [kd]
    change (ShortComplex.mk (S.map' (d + 1 - 1) (d + 1))
      (S.map' (d + 1) (d + 2)) _).Exact
    have he : d + 1 - 1 = d := by omega
    simpa only [ComposableArrows.sc, ComposableArrows.sc', ComposableArrows.obj',
      ComposableArrows.map', he] using hS.exact d
  have hepi : Epi ε := (hS.exact (d + 1)).epi_f (hlast.eq_of_tgt _ _)
  let := hepi
  let π := (ChainComplex.toSingle₀Equiv K (S.obj' (d + 2))).symm ⟨ε, hw⟩
  have hπ : QuasiIso π := by
    constructor
    intro i
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk (K.d 1 0) ε hw).Exact ∧ Epi ε
        exact ⟨hex₀, hepi⟩
      all_goals rfl
    | succ i =>
      rw [quasiIsoAt_iff_exactAt' π (i + 1)
        (ChainComplex.exactAt_succ_single_obj _ _)]
      exact hex i
  refine ⟨{ complex := K
            π := π
            quasiIso := hπ
            projective := ?_ }, ?_, hfin⟩
  · intro i
    let : Module.Free R (X i) := (hfin i).2
    infer_instance
  · exact hz

end ModuleCat
