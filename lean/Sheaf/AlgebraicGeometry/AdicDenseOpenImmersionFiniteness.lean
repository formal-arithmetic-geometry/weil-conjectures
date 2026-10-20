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
import Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.LisseEConstructibleIntegralLattice
import Sheaf.Paper.SfIntegralDirectImageConstructible

/-!
# Adic finiteness for a dense open immersion with affine source

This is the open-immersion input for the affine compactification reduction of
`sk-prop-sf-finiteness`. It concerns ordinary direct image, including its boundary stalks.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- A constructible adic sheaf on a dense affine open has bounded constructible direct image.

Source: SGA 4½, *Théorème de finitude*, Theorem 1.1 and the open-immersion paragraph of
`sk-prop-sf-finiteness`; Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.7.2,
Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-dense-open-direct-image-finiteness)

Proof: the finite-type target is noetherian and quasi-excellent, and ℓ is invertible on it.
On this target and its open subscheme, local constructibility is equivalent to a finite
lisse stratification. By Proposition 6.8.14, the sheaf in degree zero descends to a bounded
constructible complex over a finite extension E of Q_ℓ and is the rationalization of an
integral constructible complex C over O_E. This passage does not require a global lisse
lattice: Lemma 6.8.13 supplies constructible integral structures and the proof of
Proposition 6.8.14 glues them by the localization of extension groups.

For each power of a uniformizer of O_E, the reduction of C has finite torsion coefficients.
The open-immersion finiteness theorem makes its derived direct image constructible.
The torsion direct-image functor has a finite cohomological-dimension bound independent
of that power (Theorem 6.7.1); together with the two-term resolution of each coefficient
quotient, this gives a uniform finite interval for all the derived direct images of the
reductions. The complete direct image of C is derived complete, and reduction commutes
with direct image, by Lemmas 6.5.9 and 6.5.11. Lemma 6.7.2 consequently makes this integral
direct image constructible. Proposition 6.8.11 identifies this with boundedness and
constructible cohomology. Rationalization and passage to Q̄_ℓ carry this computation to
the ambient derived direct image of modules over the adic coefficient sheaf, as in
Remark 6.8.15. Thus the displayed right derived functor is bounded and all of its
cohomology sheaves are constructible. No bound by the dimensions of the fibres of the
open immersion is asserted. -/
theorem bounded_constructible_rightDerivedFunctor_adicLowerStar_of_denseOpenImmersion
    (hK : ringChar K ≠ l) {Z W : Scheme.{u}} [IsAffine Z]
    (t : W ⟶ Spec (.of K)) [LocallyOfFiniteType t] [QuasiCompact t]
    (j : Z ⟶ W) [IsOpenImmersion j] [QuasiCompact j] (hj : DenseRange j.base)
    (F : AdicSheaf l Z) (hF : IsAdicConstructibleSheaf F) :
    (_root_.DerivedCategory.TStructure.t.bounded ⊓
      _root_.DerivedCategory.homologyProperty (adicConstructibleSheaf l W))
      ((j)_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by sorry

end AlgebraicGeometry.ProEtale
