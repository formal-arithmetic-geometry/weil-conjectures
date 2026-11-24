/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsExact
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsInvariantsZero
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding

/-!
# Effaceable locally constant cochain cohomology over the integers

The cohomology of locally constant inhomogeneous cochains of discrete `ℤ`-representations of a
profinite group is an effaceable cohomological delta-functor whose degree zero part is the
invariants.

## Implementation details

The delta-functor structure comes from the degreewise short exact sequences of cochain
complexes. Effaceability uses the embedding of `M` into `LocallyConstant G M` with right
translation, whose cochain complex is exact in positive degrees.

## References

* [Stacks Project, Tag 0DVG](https://stacks.math.columbia.edu/tag/0DVG)
-/

@[expose] public section

universe u v w s

open CategoryTheory

namespace Rep

private theorem exists_homology_deltaFunctor
    {A : Type v} [Category.{w} A] [Abelian A]
    (C : A ⥤ CochainComplex AddCommGrpCat.{s} ℕ) [C.Additive]
    (hs : ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
      ((S.map C).map (HomologicalComplex.eval
        AddCommGrpCat.{s} (ComplexShape.up ℕ) n)).ShortExact) :
    ∃ T : CohomologicalDeltaFunctor A AddCommGrpCat.{s},
      T.F = (fun q ↦ C ⋙ HomologicalComplex.homologyFunctor
        AddCommGrpCat.{s} (ComplexShape.up ℕ) q) := by
  have hse (S : ShortComplex A) (hS : S.ShortExact) : (S.map C).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (hs S hS)
  let T : CohomologicalDeltaFunctor A AddCommGrpCat.{s} :=
    { F := fun q ↦ C ⋙ HomologicalComplex.homologyFunctor _ _ q
      additive := fun _ ↦ inferInstance
      delta := fun S hS n ↦ (hse S hS).δ n (n + 1) rfl
      mono_zero := by
        intro S hS
        have : Mono ((C.map S.f).f 0) := (hs S hS 0).mono_f
        exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
          (C.map S.f) 0 (by
            intro i hi
            change i + 1 = 0 at hi
            omega)
      exact_middle := by
        intro S hS n
        exact ⟨_, (hse S hS).homology_exact₂ n⟩
      exact_right := by
        intro S hS n
        exact ⟨_, (hse S hS).homology_exact₃ n (n + 1) rfl⟩
      exact_left := by
        intro S hS n
        exact ⟨_, (hse S hS).homology_exact₁ n (n + 1) rfl⟩
      naturality := by
        intro S R hS hR φ n
        exact HomologicalComplex.HomologySequence.δ_naturality
          (C.mapShortComplex.map φ) (hse S hS) (hse R hR) n (n + 1) rfl }
  exact ⟨T, rfl⟩

/-- Let `G` be a compact totally disconnected group and `A` an abelian category equivalent to
discrete `ℤ`-representations of `G`. There is a functor `C` from `A` to cochain complexes whose
terms are the locally constant cochains `G^n → E M`, with the inhomogeneous differential, and
whose cohomology is an effaceable cohomological delta-functor with degree zero isomorphic to
the invariants. -/
theorem exists_locallyConstantCochains_effaceable
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    : ∃ C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ,
      ∃ e : ∀ (M : A) (n : ℕ),
          (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V,
        (∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
          e N n (((C.map f).f n) x) g =
            (E.functor.map f).hom.hom (e M n x g)) ∧
        (∀ (M : A) (n : ℕ) (x : (C.obj M).X n) (g : Fin (n + 1) → G),
          e M (n + 1) (((C.obj M).d n (n + 1)) x) g =
            (E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
              ∑ k : Fin (n + 1),
                (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g)) ∧
        ∃ T : CohomologicalDeltaFunctor A AddCommGrpCat.{max u s},
          T.F = (fun q ↦ C ⋙ HomologicalComplex.homologyFunctor
            AddCommGrpCat.{max u s} (ComplexShape.up ℕ) q) ∧
          Nonempty (T.F 0 ≅
            (E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
              forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat)) ∧
          (∀ (n : ℕ), 0 < n → ∀ (M : A),
            ∃ (N : A) (f : M ⟶ N), Mono f ∧ (T.F n).map f = 0) := by
  obtain ⟨C, e, hm, hd, ha, hs⟩ := exists_locallyConstantCochains_exact G A E
  have : C.Additive := ha
  obtain ⟨T, hT⟩ := exists_homology_deltaFunctor C hs
  refine ⟨C, e, hm, hd, T, hT, ?_, ?_⟩
  · rw [hT]
    exact locallyConstantCochains_invariants_zero G A E C e hm hd
  · intro n hn M
    obtain ⟨N, f, hf, hN⟩ :=
      locallyConstantCochains_acyclic_embedding G A E C e hm hd M
    refine ⟨N, f, hf, ?_⟩
    rw [hT]
    exact ((hN n hn).isZero_homology).eq_of_tgt _ _

end Rep
