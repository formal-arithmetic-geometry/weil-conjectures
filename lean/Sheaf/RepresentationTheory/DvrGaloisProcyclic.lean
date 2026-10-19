/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.RepresentationTheory.ProcyclicTwoTerm
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Vanishing and finiteness from the procyclic two-term computation

Source: blueprint main-20261015, `lem-exc-dvr-galois.proof.md`, final paragraph.
(blueprint: lem-exc-procyclic-cohomology-conclusions)
-/

@[expose] public section
set_option autoImplicit false

universe v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

private theorem finite_homology_of_finite_term {A : Type v} [Ring A]
    (K : CochainComplex (ModuleCat.{w} A) ℕ) (q : ℕ) [Finite (K.X q)] :
    Finite (K.homology q) := by
  let S := K.sc q
  have : Finite S.X₂ := ‹Finite (K.X q)›
  have : Finite (LinearMap.ker S.g.hom) := inferInstance
  have : Finite (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have : Finite S.moduleCatLeftHomologyData.H :=
    (inferInstance : Finite (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles))
  exact Finite.of_equiv _ S.moduleCatHomologyIso.toLinearEquiv.toEquiv.symm

/-- The procyclic two-term computation gives higher vanishing and low-degree finiteness.

Proof: in degrees above one the computing complex has zero terms, hence zero homology.
If M is finite, its degree-zero and degree-one terms are finite by the given linear
identifications. Homology in either degree is a quotient of the submodule of cycles
in that finite term, and is finite. Transport these assertions across the cohomology
comparison isomorphisms.

Source: blueprint main-20261015, `lem-exc-dvr-galois.proof.md`, final paragraph.
(blueprint: lem-exc-procyclic-cohomology-conclusions) -/
theorem procyclic_cohomology_conclusions
    (l : ℕ) [Fact l.Prime] (s : ℕ) (A : Type v) [Ring A] [Finite A]
    (hA : (l ^ s : ℕ) • (1 : A) = 0)
    (M : DiscreteContinuousRep.{v, 0, w} A (Multiplicative ℤ_[l])) :
    (∀ q : ℕ, 1 < q →
      IsZero ((discreteContinuousCohomologyFunctor.{0,v,w}
        (Multiplicative ℤ_[l]) A q).obj M)) ∧
      (Finite M.obj.V →
        Finite (((discreteContinuousCohomologyFunctor.{0,v,w}
          (Multiplicative ℤ_[l]) A 0).obj M).carrier) ∧
        Finite (((discreteContinuousCohomologyFunctor.{0,v,w}
          (Multiplicative ℤ_[l]) A 1).obj M).carrier)) := by
  obtain ⟨K, e₀, e₁, _, _, _, hzero, hiso⟩ :=
    exists_procyclic_twoTerm_computation l s A hA
  constructor
  · intro q hq
    let e := (hiso q).some.app M
    exact (HomologicalComplex.ExactAt.of_isZero (hzero M q (by omega))).isZero_homology
      |>.of_iso e
  · intro hM
    have : Finite ((K.obj M).X 0) := Finite.of_equiv M.obj.V (e₀ M).toEquiv.symm
    have : Finite ((K.obj M).X 1) := Finite.of_equiv M.obj.V (e₁ M).toEquiv.symm
    constructor
    · have := finite_homology_of_finite_term (K.obj M) 0
      have : Finite ((K ⋙ HomologicalComplex.homologyFunctor
          (ModuleCat.{w} A) (ComplexShape.up ℕ) 0).obj M) := this
      exact Finite.of_equiv _ ((hiso 0).some.app M).toLinearEquiv.toEquiv.symm
    · have := finite_homology_of_finite_term (K.obj M) 1
      have : Finite ((K ⋙ HomologicalComplex.homologyFunctor
          (ModuleCat.{w} A) (ComplexShape.up ℕ) 1).obj M) := this
      exact Finite.of_equiv _ ((hiso 1).some.app M).toLinearEquiv.toEquiv.symm

end Rep
