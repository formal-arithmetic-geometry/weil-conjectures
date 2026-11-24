/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-! # Bounded models for one degree of algebraic residue fibres

## References

* Stacks Project, Tag 0BDI
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Stupid truncation makes a bounded-above finite-free complex bounded while preserving
one degree of cohomology after every residue-field extension (Stacks, Tag 0BDI). -/
theorem exists_bounded_finiteFree_fiber_model (A : Type u) [CommRing A]
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) (hb : F.IsStrictlyLE b)
    (hfree : ∀ n : ℤ, Module.Free A (F.X n) ∧ Module.Finite A (F.X n)) (i : ℤ) :
    ∃ K : CochainComplex (ModuleCat.{u} A) ℤ,
      (∃ a c : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE c) ∧
      (∀ n : ℤ, Module.Free A (K.X n) ∧ Module.Finite A (K.X n)) ∧
      ∀ p : PrimeSpectrum A,
        Module.finrank p.asIdeal.ResidueField
          ((((ModuleCat.extendScalars (algebraMap A p.asIdeal.ResidueField)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F).homology i) =
        Module.finrank p.asIdeal.ResidueField
          ((((ModuleCat.extendScalars (algebraMap A p.asIdeal.ResidueField)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).homology i) := by
  classical
  let K := F.stupidTrunc (ComplexShape.embeddingUpIntGE (i - 1))
  have := hb
  refine ⟨K, ⟨i - 1, b, inferInstance, inferInstance⟩, ?_, ?_⟩
  · intro n
    by_cases hn : n < i - 1
    · have hzero : CategoryTheory.Limits.IsZero (K.X n) :=
        F.isZero_stupidTrunc_X _ n
          ((ComplexShape.notMem_range_embeddingUpIntGE_iff (i - 1) n).mpr hn)
      let := ModuleCat.subsingleton_of_isZero hzero
      exact ⟨inferInstance, inferInstance⟩
    · have he : (ComplexShape.embeddingUpIntGE (i - 1)).f (n - (i - 1)).toNat = n := by
        change i - 1 + ((n - (i - 1)).toNat : ℤ) = n
        omega
      let e := (F.stupidTruncXIso _ he).toLinearEquiv
      have := (hfree n).1
      have := (hfree n).2
      exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
  · intro p
    let T := ModuleCat.extendScalars (algebraMap A p.asIdeal.ResidueField)
    let FT := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
    let KT := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    have he (n : ℤ) (hn : i - 1 ≤ n) :
        (ComplexShape.embeddingUpIntGE (i - 1)).f (n - (i - 1)).toNat = n := by
      change i - 1 + ((n - (i - 1)).toNat : ℤ) = n
      omega
    let e (n : ℤ) (hn : i - 1 ≤ n) : K.X n ≅ F.X n :=
      F.stupidTruncXIso _ (he n hn)
    have hd (n m : ℤ) (hn : i - 1 ≤ n) (hm : i - 1 ≤ m) :
        (e n hn).hom ≫ F.d n m = K.d n m ≫ (e m hm).hom := by
      dsimp [K, e, HomologicalComplex.stupidTruncXIso, HomologicalComplex.stupidTrunc]
      rw [HomologicalComplex.extend_d_eq _ _ (he n hn) (he m hm),
        HomologicalComplex.restriction_d_eq _ _ (he n hn) (he m hm)]
      simp [Category.assoc, HomologicalComplex.restrictionXIso]
    let eT (n : ℤ) (hn : i - 1 ≤ n) : KT.X n ≅ FT.X n := T.mapIso (e n hn)
    have hdT (n m : ℤ) (hn : i - 1 ≤ n) (hm : i - 1 ≤ m) :
        (eT n hn).hom ≫ FT.d n m = KT.d n m ≫ (eT m hm).hom := by
      change T.map (e n hn).hom ≫ T.map (F.d n m) =
        T.map (K.d n m) ≫ T.map (e m hm).hom
      rw [← T.map_comp, ← T.map_comp, hd n m hn hm]
    let esc : KT.sc' (i - 1) i (i + 1) ≅ FT.sc' (i - 1) i (i + 1) :=
      ShortComplex.isoMk (eT (i - 1) (by omega)) (eT i (by omega))
        (eT (i + 1) (by omega)) (hdT _ _ (by omega) (by omega))
          (hdT _ _ (by omega) (by omega))
    let eh : KT.homology i ≅ FT.homology i :=
      ShortComplex.homologyMapIso
        (KT.isoSc' (i - 1) i (i + 1) (by simp) (by simp) ≪≫ esc ≪≫
          (FT.isoSc' (i - 1) i (i + 1) (by simp) (by simp)).symm)
    exact eh.toLinearEquiv.finrank_eq.symm

end AlgebraicGeometry.Scheme
