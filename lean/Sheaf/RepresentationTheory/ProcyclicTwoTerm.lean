/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Q33
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Sheaf.RepresentationTheory.ProcyclicComplex
import Sheaf.RepresentationTheory.ProcyclicTwoTermComparison

/-!
# Two-term continuous cohomology of the additive l-adic integers

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer/lem-exc-procyclic-two-term,
statement and proof (blueprint: lem-exc-procyclic-two-term).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- Continuous cohomology of discrete modules over the additive group of l-adic integers
is computed, naturally in coefficients, by the two-term complex with differential `τ - 1`.
Here `Multiplicative` only converts the additive group to the convention of `Rep`;
`Multiplicative.ofAdd (1 : ℤ_[l])` is the specified additive generator, not the group identity.
The equivalences `e₀` and `e₁` identify the two nonzero terms with the coefficient module,
and their naturality equations specify the same coefficient map in both degrees.
The final natural isomorphisms identify the complex's cohomology with the recorded right
derived functors of invariants in every degree.

Proof:
1. Construct the functor K explicitly, with M in degrees zero and one, differential
   τ - 1, the original coefficient map in both degrees, and zero terms above one.
2. A vector fixed by τ is invariant: its orbit map is locally constant and agrees with
   the constant vector on the dense nonnegative integers. Thus H⁰(K(-)) is naturally
   invariants. Degreewise exactness and the homology long exact sequence give a
   cohomological delta-functor.
3. Embed M into the translation module of locally constant functions by its orbit map.
   A function has period l^r. On l^(r+s) residues its total sum is l^s times a sum,
   hence zero; partial sums therefore give a periodic primitive, including at the
   last residue. Translation minus identity is surjective on the coinduced module.
4. This embedding effaces degree one, and all higher terms already vanish. The
   two-term delta-functor is universal by the effaceability criterion. The right
   derived invariant functors form a universal delta-functor as well, with the same
   degree-zero invariant functor.
5. Extend the degree-zero isomorphism and its inverse by universality. Uniqueness
   makes both composites identities, giving natural cohomology isomorphisms in all
   degrees. Supply these and the explicit term identifications in the statement.

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer/lem-exc-procyclic-two-term,
statement and all three proof paragraphs (blueprint: lem-exc-procyclic-two-term). -/
theorem exists_procyclic_twoTerm_computation
    (l : ℕ) [Fact l.Prime] (s : ℕ) (A : Type u) [Ring A] [Finite A]
    (hA : (l ^ s : ℕ) • (1 : A) = 0) :
    ∃ K : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]) ⥤
        CochainComplex (ModuleCat.{w} A) ℕ,
      ∃ (e₀ : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
          (K.obj M).X 0 ≃ₗ[A] M.obj.V)
        (e₁ : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
          (K.obj M).X 1 ≃ₗ[A] M.obj.V),
        (∀ (M N : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
          (f : M ⟶ N) (x : (K.obj M).X 0),
          e₀ N (((K.map f).f 0).hom x) = f.hom.hom (e₀ M x)) ∧
        (∀ (M N : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
          (f : M ⟶ N) (x : (K.obj M).X 1),
          e₁ N (((K.map f).f 1).hom x) = f.hom.hom (e₁ M x)) ∧
        (∀ (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
          (x : (K.obj M).X 0),
          e₁ M (((K.obj M).d 0 1).hom x) =
            M.obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l])) (e₀ M x) - e₀ M x) ∧
        (∀ (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
          (n : ℕ), 2 ≤ n → IsZero ((K.obj M).X n)) ∧
        ∀ q : ℕ, Nonempty
          (discreteContinuousCohomologyFunctor.{0, u, w} (Multiplicative ℤ_[l]) A q ≅
            K ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{w} A) (ComplexShape.up ℕ) q) := by
  let K := actionTwoTerm.{u, 0, w} A (Multiplicative ℤ_[l])
    (Multiplicative.ofAdd (1 : ℤ_[l]))
  refine ⟨K, actionTwoTermEquivZero _ _ _, actionTwoTermEquivOne _ _ _, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro M N f x
    rfl
  · intro M N f x
    rfl
  · intro M x
    rfl
  · intro M n hn
    exact actionTwoTerm_isZero _ _ _ _ _ hn
  · intro q
    exact procyclic_twoTerm_cohomology_comparison l s A hA q

end Rep
