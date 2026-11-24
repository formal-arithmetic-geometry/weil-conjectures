/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleDescent
import WeilConjectures.AlgebraicGeometry.FlatModuleDescentAffineCharts

/-!
# Eventual descent of flatness for finitely presented scheme modules

## Implementation details

The ring functor presents the affine inverse system contravariantly. The cone supplies
its limit projections. An affine limit is written as `IsAffine c.pt`, allowing any choice
of its isomorphism with a spectrum.

## References

* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A finitely presented quasi-coherent module whose limit pullback is flat over the base
is flat over every sufficiently late base (Stacks, Tag 05LY). -/
theorem exists_eventually_isFlatOver_of_limit
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : Xi.Modules) [M.IsFinitePresentation] [M.IsQuasicoherent]
    (hflat : Scheme.Modules.IsFlatOver
      ((Scheme.Modules.tensorPullback (pullback.fst f (c.π.app (op i)))).obj M)
      (pullback.snd f (c.π.app (op i)))) :
    ∃ j : I, ∃ hij : i ≤ j, ∀ (k : I) (hjk : j ≤ k),
      Scheme.Modules.IsFlatOver
        ((Scheme.Modules.tensorPullback
          (pullback.fst f (Spec.map (R.map (homOfLE (hij.trans hjk)))))).obj M)
        (pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk))))) := by
  open scoped TensorProduct in
    classical
    obtain ⟨n, B, N, a, hB, hN, hlimit, hstage⟩ :=
      exists_flat_module_descent_affine_charts R c hc i f M hflat
    have hdescent (b : Fin n) : ∃ j : I, i ≤ j ∧
        ∀ (k : I) (hij : i ≤ j) (hjk : j ≤ k),
          (letI : Module (R.obj i : Type u) (N b) := Module.compHom _ (a b)
          letI : Algebra (R.obj i : Type u) (R.obj k : Type u) :=
            (R.map (homOfLE (hij.trans hjk))).hom.toAlgebra
          letI : Algebra (R.obj i : Type u)
              ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u)) :=
            Algebra.TensorProduct.rightAlgebra
          letI : Module (R.obj i : Type u)
              ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u)) :=
            Algebra.toModule
          Module.Flat ((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u))
            (((R.obj k : Type u) ⊗[(R.obj i : Type u)] (R.obj i : Type u))
              ⊗[(R.obj i : Type u)] (N b))) := by
      let := (a b).toAlgebra
      let := hB b
      let := hN b
      exact exists_eventually_flat_of_finitePresentation (Ni := (N b : Type u))
        R (colimit.cocone R)
        (colimit.isColimit R) (Algebra.ofId (R.obj i : Type u) (B b : Type u)) (hlimit b)
    choose j hij hj using hdescent
    have hbound (s : Finset (Fin n)) : ∃ k : I, i ≤ k ∧ ∀ b ∈ s, j b ≤ k := by
      induction s using Finset.induction_on with
      | empty => exact ⟨i, le_rfl, by simp⟩
      | @insert b s _ ih =>
        obtain ⟨k, hik, hk⟩ := ih
        obtain ⟨l, hkl, hbl⟩ := exists_ge_ge k (j b)
        refine ⟨l, hik.trans hkl, ?_⟩
        intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hbl
        · exact (hk d hd).trans hkl
    obtain ⟨k, hik, hk⟩ := hbound Finset.univ
    refine ⟨k, hik, ?_⟩
    intro l hkl
    apply hstage l (hik.trans hkl)
    intro b
    exact hj b l (hij b) ((hk b (Finset.mem_univ b)).trans hkl)

end AlgebraicGeometry
