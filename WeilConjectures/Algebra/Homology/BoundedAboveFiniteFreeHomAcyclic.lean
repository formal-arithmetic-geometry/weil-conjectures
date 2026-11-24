/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Algebra.Homology.FiniteFreeInternalHomExactSequence
import WeilConjectures.Algebra.Homology.BoundedHomExactColumns

/-! # Hom from bounded-above finite free complexes preserves bounded-below acyclicity

## References

* Stacks Project, cohomology.tex, Tag 0GM8 (Lemma 20.51.4), case (2)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The total sheaf Hom from a bounded-above complex with finite free terms to a
bounded-below acyclic complex is acyclic. -/
theorem acyclic_homComplex_of_boundedAbove_finiteFree
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R : Sheaf J CommRingCat.{w}}
    (E A : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hEbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hEfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅ SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
      (ULift.{w} (Fin r))))
    (hAbounded : ∃ M : ℤ, ∀ q : ℤ, q < M → IsZero (A.X q))
    (hAacyclic : A.Acyclic) : (CategoryTheory.homComplex E A).Acyclic := by
  obtain ⟨N, hN⟩ := hEbounded
  obtain ⟨M, hM⟩ := hAbounded
  apply acyclic_homComplex_of_bounded_exact_columns E A N M hN hM
  intro p q
  obtain ⟨r, ⟨e⟩⟩ := hEfree p
  exact finiteFree_internalHom_exact_sequence (E.X p) r e (A.sc q) (hAacyclic q)

end CochainComplex
