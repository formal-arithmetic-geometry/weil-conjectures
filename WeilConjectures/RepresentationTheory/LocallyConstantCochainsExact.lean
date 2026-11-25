/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsStructure
import WeilConjectures.RepresentationTheory.LocallyConstantCochainsDegreewiseExact


/-!
# Exactness of the locally constant cochain functor

The functor of locally constant inhomogeneous cochains of discrete `ℤ`-representations of a
profinite group is additive and degreewise exact.

## References

* [Stacks Project, Tag 0DVG](https://stacks.math.columbia.edu/tag/0DVG)
-/

@[expose] public section

universe u v w s

open CategoryTheory

namespace Rep

/-- Let `G` be a compact totally disconnected group and `A` an abelian category equivalent to
discrete `ℤ`-representations of `G`. There is an additive functor `C` from `A` to cochain
complexes whose terms are the locally constant cochains `G^n → E M`, with the inhomogeneous
differential, and which sends short exact sequences to degreewise short exact sequences. -/
theorem exists_locallyConstantCochains_exact
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
        ∃ a : C.Additive,
          letI := a
          ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
            ((S.map C).map (HomologicalComplex.eval
              AddCommGrpCat.{max u s} (ComplexShape.up ℕ) n)).ShortExact := by
  obtain ⟨C, e, hm, hd⟩ := exists_locallyConstantCochains_structure G A E
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have ha : C.Additive := by
    constructor
    intro M N f h
    ext n x
    apply (e N n).injective
    ext g
    change e N n (((C.map (f + h)).f n) x) g =
      e N n (((C.map f).f n) x + ((C.map h).f n) x) g
    simp only [map_add, LocallyConstant.add_apply]
    rw [hm, hm, hm]
    rw [Functor.map_add]
    rfl
  let := ha
  exact ⟨C, e, hm, hd, ha, locallyConstantCochains_degreewise_exact G A E C e hm⟩

end Rep
