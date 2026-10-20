/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.FiniteType
import Sheaf.AlgebraicGeometry.BertiniAffineIncidenceChart
import Sheaf.AlgebraicGeometry.LinearIncidenceIrreducible
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Irreducible trivialized affine incidence charts

Source: Stacks Project, More on Morphisms, Tag 0G4F, middle proof paragraph.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme.Modules

/-- A nonzero system of sections on a trivialized affine line bundle has irreducible
universal incidence scheme if its base ideal has codimension at least two.

Source: Stacks Project, More on Morphisms, Tag 0G4F, middle proof paragraph.
(blueprint: lem-zl-bertini-affine-incidence-irreducible).

Proof: Enumerate the finite index type. The coefficient ideal is unchanged by this
bijection, and variable renaming carries the incidence polynomial to the enumerated one.
The affine linear-incidence theorem makes the latter quotient spectrum irreducible.
Transport through the quotient renaming isomorphism and the proved affine incidence chart.
The nonzero coefficient assumption also ensures that the index type is nonempty. -/
theorem irreducibleSpace_bertiniAffineIncidence
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IsDomain A]
    (L : (Spec (.of A)).Modules) [L.IsInvertible]
    {e : Γ(L, ⊤)} (he : IsFreeGenerator e)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤))
    (hf : ∃ i, (Scheme.ΓSpecIso (.of A)).hom (he.coeff (s i)) ≠ 0)
    (hJ : ∀ p : Ideal A,
      p ∈ (Ideal.span (Set.range
        (fun i ↦ (Scheme.ΓSpecIso (.of A)).hom (he.coeff (s i))))).minimalPrimes →
      (2 : ℕ∞) ≤ p.height) :
    IrreducibleSpace ((bertiniUniversalIdeal
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) L s).subscheme) := by
  classical
  let c : I → A := fun i ↦ (Scheme.ΓSpecIso (.of A)).hom (he.coeff (s i))
  let eI := Fintype.equivFin I
  let f : Fin (Fintype.card I) → A := fun j ↦ c (eI.symm j)
  have hr : 0 < Fintype.card I := by
    obtain ⟨i, _⟩ := hf
    exact Fintype.card_pos_iff.mpr ⟨i⟩
  have hf' : ∃ j, f j ≠ 0 := by
    obtain ⟨i, hi⟩ := hf
    exact ⟨eI i, by simpa [f, c] using hi⟩
  have hRange : Set.range f = Set.range c := by
    ext a
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨eI.symm j, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨eI i, by simp [f]⟩
  have hJ' : ∀ p : Ideal A, p ∈ (Ideal.span (Set.range f)).minimalPrimes →
      (2 : ℕ∞) ≤ p.height := by
    simpa only [hRange] using hJ
  let P := Ideal.span {∑ i, MvPolynomial.C (c i) * MvPolynomial.X i}
  let Q := Ideal.span {∑ j, MvPolynomial.C (f j) * MvPolynomial.X j}
  have hpoly : MvPolynomial.renameEquiv A eI
      (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) =
      ∑ j, MvPolynomial.C (f j) * MvPolynomial.X j := by
    simp only [map_sum, map_mul, MvPolynomial.renameEquiv_apply,
      MvPolynomial.rename_C, MvPolynomial.rename_X]
    exact Fintype.sum_equiv eI _ _ (fun i ↦ by simp [f])
  have hQ : Q = P.map (MvPolynomial.renameEquiv A eI).toRingHom := by
    dsimp only [P, Q]
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    exact congrArg Set.singleton hpoly.symm
  let eqv := Ideal.quotientEquiv P Q (MvPolynomial.renameEquiv A eI).toRingEquiv hQ
  have hIrred : IrreducibleSpace
      (Spec (.of (MvPolynomial (Fin (Fintype.card I)) A ⧸ Q))) :=
    linear_incidence_irreducible k A (Fintype.card I) hr f hf' hJ'
  obtain ⟨eH, _⟩ := exists_bertiniAffineIncidenceChart k A L he s
  let eQ := Scheme.Spec.mapIso eqv.toCommRingCatIso.symm.op
  exact (Scheme.homeoOfIso (eH ≪≫ eQ)).irreducibleSpace_iff.mpr hIrred

end AlgebraicGeometry
