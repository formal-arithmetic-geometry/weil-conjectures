/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.LisseLatticeHeartLiftData

/-! # Integral membership and exact degree-zero localization for arbitrary lattice choices. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.LisseLattice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Integral membership and exact degree-zero localization for arbitrary lattice choices.
Source: Bhatt--Scholze, Proposition 6.8.11(3), Lemma 6.8.2 and Remark 6.8.15.

Proof: N is constructible by its finite stratification of finitely presented local
models. Its single complex has only N as nonzero cohomology, so condition (iii) of the
integral stratified-perfect characterization and normalized coefficient transport give
hN. Every quasi-compact etale chart is finite type over the same field, hence noetherian
and finite dimensional. Ordinary inverse image there is exact slice restriction, with
the coefficient map fixed on finite quotients. It preserves constructibility, either
by restriction of the stratification or ordinary-completed pullback preservation;
this gives hNi. Each finite locally free M has a one-stratum presentation, locally
the scalar extension of the finitely presented free module R^r, so the same criterion
gives hMi. Exact localization identifies its left derived functor with the termwise
ordinary functor. For every single complex, the derived tensor counit followed by the
single-complex comparison is therefore invertible. Composing with a.integral gives
exactly singleComparison, and proves all three displayed isomorphism assertions.
No flatness assumption on N is used: localization itself is exact. Zero ranks and
torsion finitely presented local models are included.
(blueprint: lem-tw-lisse-lattice-single-comparisons). -/
theorem lattice_single_comparisons (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (a : Realizations l E) (X : LisseRealization.Base D l hl)
    (L : RationalModules l E X.scheme) (c : Choice l E a X.scheme L) :
    ∃ hN : sfIntegralConstructible l E X.scheme
        ((DerivedCategory.singleFunctor _ 0).obj c.N),
      IsIso ((a.realization X.scheme).singleComparison l E c.N hN) ∧
      ∀ i : c.I,
        ∃ hNi : sfIntegralConstructible l E (c.Y i).left
            ((DerivedCategory.singleFunctor _ 0).obj ((integralPull l E (c.Y i).hom).obj c.N)),
        ∃ hMi : sfIntegralConstructible l E (c.Y i).left
            ((DerivedCategory.singleFunctor _ 0).obj (c.M i)),
          IsIso ((a.realization (c.Y i).left).singleComparison l E
            ((integralPull l E (c.Y i).hom).obj c.N) hNi) ∧
          IsIso ((a.realization (c.Y i).left).singleComparison l E (c.M i) hMi) := by sorry

end WeilConjectures.LisseLattice
