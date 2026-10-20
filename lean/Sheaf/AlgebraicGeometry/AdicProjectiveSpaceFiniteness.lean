/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ProperBoundedConstructible
import Sheaf.AlgebraicGeometry.ProperCaseConstructibility
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.LisseEConstructibleIntegralLattice
import Sheaf.Paper.SfIntegralDirectImageConstructible

/-!
# Adic finiteness for projection from relative projective space

This is the proper input for the affine compactification reduction of
`sk-prop-sf-finiteness`. Its source is a constructible sheaf in degree zero; the existing
truncation dévissage extends the result to bounded constructible complexes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

open Scheme

/-- Projection from finite-dimensional projective space over an affine finite-type base
has bounded constructible direct image on constructible adic sheaves.

Source: the proper-case paragraph of `sk-prop-sf-finiteness`, SGA 4½, *Théorème de finitude*,
Theorem 1.1; Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-projective-space-direct-image-finiteness)

Proof: the projection p is proper and finitely presented between noetherian schemes,
and its fibres are projective spaces of dimension equal to the cardinality of n.
Use Proposition 6.8.14 to express F[0] over some finite coefficient extension E/Q_ℓ as
the rationalization of an integral constructible complex C. Existence of such an
integral structure follows from the constructible-lattice argument of Lemma 6.8.13;
it does not require a global lisse lattice.

For a uniformizer π of O_E, each derived reduction C_n modulo π^n has finite torsion
coefficients and is bounded constructible. Classical proper finiteness gives
constructibility of Rp_* C_n. Proper base change and the cohomological-dimension bound
for projective-space fibres give a bound independent of n; combined with the fixed
amplitude of C and the two-term resolution of O_E/π^n, this bounds the entire tower in
a fixed finite interval. The complete direct image commutes with the inverse limit
and with these perfect reductions (Lemmas 6.5.9 and 6.5.11). Lemma 6.7.2 therefore
puts Rp_* C in the integral constructible category. By Proposition 6.8.11 it is bounded
with constructible cohomology. Rationalization, finite coefficient descent, and
Remark 6.8.15 identify its scalar extension with the ambient right derived functor
on AdicSheaf in the conclusion and preserve these properties. This proves the claim.
The empty base causes no exception: every sheaf there is zero. The case n empty is
projective zero-space and the same argument applies. -/
theorem bounded_constructible_rightDerivedFunctor_adicLowerStar_projectiveSpace
    (hK : ringChar K ≠ l) {W : Scheme.{u}} [IsAffine W]
    (t : W ⟶ Spec (.of K)) [LocallyOfFiniteType t] (n : Type u) [Finite n]
    (F : AdicSheaf l ℙ(Option n; W)) (hF : IsAdicConstructibleSheaf F) :
    (_root_.DerivedCategory.TStructure.t.bounded ⊓
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l W))
      ((ℙ(Option n; W) ↘ W)_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by sorry

end AlgebraicGeometry.ProEtale
