/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker E6
-/
module

public import Sheaf.RepresentationTheory.ProcyclicComplex
public import Sheaf.CategoryTheory.DiscreteModulesAbelian
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding
import Sheaf.RepresentationTheory.ProcyclicPrimitive
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Effacement of positive two-term cohomology

Source: blueprint lem-exc-procyclic-two-term, third proof paragraph.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace Rep

set_option linter.style.haveILetI false in
/-- Positive two-term cohomology is effaced by continuous coinduction.

Proof: embed the coefficient module by its orbit map into the right-translation module
of locally constant functions. The periodic primitive theorem makes translation minus
identity surjective there. Thus degree-one homology is zero. All higher terms are zero,
so their homology vanishes as well. Evaluation at one shows the orbit map is injective,
and hence monic. Its induced map to the zero positive cohomology is zero.

Source: blueprint lem-exc-procyclic-two-term, third proof paragraph
(blueprint: lem-exc-procyclic-two-term-effacement). -/
theorem actionTwoTerm_effaceable
    (l : ℕ) [Fact l.Prime] (s : ℕ) (A : Type u) [Ring A] [Finite A]
    (hA : (l ^ s : ℕ) • (1 : A) = 0) :
    let h := Classical.choose (discreteModules_abelian.{0, u, w} (Multiplicative ℤ_[l]) A)
    letI := h
    letI : Preadditive (DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l])) :=
      h.toPreadditive
    ∀ T : CohomologicalDeltaFunctor
        (DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l])) (ModuleCat.{w} A),
      T.F = (fun q ↦ actionTwoTerm A (Multiplicative ℤ_[l])
        (Multiplicative.ofAdd (1 : ℤ_[l])) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{w} A) (ComplexShape.up ℕ) q) →
      ∀ q : ℕ, 0 < q → ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
        ∃ (N : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l])) (f : M ⟶ N),
          Mono f ∧ (T.F q).map f = 0 := by
  classical
  dsimp only
  intro T hT q hq M
  obtain ⟨D, e, ι, hD, _, _, hinj⟩ :=
    exists_coinduced_discrete_embedding.{0, u, w} (Multiplicative ℤ_[l]) A
  have hm : Mono (ι.app M) := by
    constructor
    intro Z f g hfg
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply hinj M
    exact congrArg (fun k ↦ k.hom.hom x) hfg
  refine ⟨D.obj M, ι.app M, hm, ?_⟩
  let K := (actionTwoTerm.{u, 0, w} A (Multiplicative ℤ_[l])
    (Multiplicative.ofAdd (1 : ℤ_[l]))).obj (D.obj M)
  have hz : IsZero (K.homology q) := by
    by_cases hqone : q = 1
    · subst q
      have hs : Function.Surjective (K.d 0 1).hom := by
        intro y
        let f : LocallyConstant ℤ_[l] M.obj.V :=
          ⟨fun x ↦ e M y (Multiplicative.ofAdd x), (e M y).isLocallyConstant⟩
        have htors (m : M.obj.V) : (l ^ s) • m = 0 := by
          have ht := congrArg (fun a : A ↦ a • m) hA
          simpa only [smul_assoc, one_smul, zero_smul] using ht
        obtain ⟨h, hh⟩ := exists_procyclic_primitive l s M.obj.V htors f
        let h' : LocallyConstant (Multiplicative ℤ_[l]) M.obj.V :=
          ⟨fun x ↦ h (Multiplicative.toAdd x), h.isLocallyConstant⟩
        refine ⟨(e M).symm h', ?_⟩
        apply (e M).injective
        ext x
        change e M ((D.obj M).obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l]))
          ((e M).symm h') - (e M).symm h') x = e M y x
        rw [map_sub, LocallyConstant.sub_apply, hD, LinearEquiv.apply_symm_apply]
        exact hh (Multiplicative.toAdd x)
      have : Epi (K.d 0 1) := (ModuleCat.epi_iff_surjective _).mpr hs
      apply HomologicalComplex.ExactAt.isZero_homology
      rw [K.exactAt_iff' 0 1 2 (by simp) (by simp)]
      apply (ShortComplex.exact_iff_epi _ ?_).mpr
      · exact this
      · rfl
    · exact (HomologicalComplex.ExactAt.of_isZero
        (actionTwoTerm_isZero A (Multiplicative ℤ_[l])
          (Multiplicative.ofAdd (1 : ℤ_[l])) (D.obj M) q (by omega))).isZero_homology
  rw [hT]
  exact hz.eq_of_tgt _ _

end Rep
