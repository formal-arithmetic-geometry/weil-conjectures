/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Iso
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.AlgebraicGeometry.HypercohomologyFiltrations

/-!
# Half-plane convergence of the hypercohomology spectral sequences

Source: blueprint `sec-proper-base-change/sk-thm-properbasechange`, order 1376;
Stacks Project, Tags 0DDE, 015J, 0132, 012W, 0BDV
(blueprint: lemma-weil-pbc-hypercohomology-convergence).
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

open CategoryTheory

/--
The two canonical truncation spectral sequences of a torsion bounded-below étale
complex are half-plane spectral sequences.  In each total degree their image
filtration is finite, exhaustive, separated, and convergent without a derived
inverse-limit condition.

Source: blueprint `sec-proper-base-change/sk-thm-properbasechange`, order 1376;
Stacks Project, Tags 0DDE, 015J, 0132, 012W, 0BDV
(blueprint: lemma-weil-pbc-hypercohomology-convergence).

Proof: apply the right-derived negative-vanishing theorem to the truncation
couples for `f` and `f'` (and exactness of inverse image for the base-change
comparison), obtaining the bounds `p ≥ 0` and `q ≥ a`.  On a fixed diagonal
`p + q = n` these bounds give the finite interval `a ≤ q ≤ n`.  The finite
image filtrations from the truncation tower are therefore exhaustive and
separated, and the half-plane convergence theorem identifies their associated
graded pieces with the stabilized page; the quotient tower is eventually
constant, so no derived inverse-limit hypothesis is required.

Rendering: for each sequence the abutment `Hⁿ` is an `AlphaColimit` whose object is
the actual derived homology `Hⁿ(F K)` and whose cocone maps are the recorded
`hypercohomologyAbutmentMap`s.  Its image filtration [def-sp-filtration] is finite
(`IsFinite`: a whole step and a zero step, hence exhaustive and separated); transported
to `Hⁿ(F K)` its steps are `FᵖHⁿ = im(Hⁿ(F τ≤(n-p) K) → Hⁿ(F K))`, the defining steps
of `hypercohomologyFiltration` [def-weil-pbc-hypercohomology-filtrations]; and the
couple `ConvergesTo` it [def-sp-convergence].  The page index `r` is the page `E_(r+2)`.
-/
theorem hypercohomology_convergence_statement
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : ChosenCartesianSquare g' f' f g)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Q.obj K.obj ≅ L.obj)
    (hT : ∀ q : ℤ, CategoryTheory.Sheaf.IsTorsion
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (a : ℤ) (ha : ∀ q : ℤ, q < a → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (hterms : ∀ i : ℤ, i < a → IsZero (K.obj.X i)) :
    (∀ (r : ℕ) (p q : ℤ), (p < 0 ∨ q < a) →
      IsZero (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageCouple r).E p q)) ∧
    (∀ (r : ℕ) (n p q : ℤ), p + q = n →
      ¬ IsZero (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).pageCouple r).E p q) →
      a ≤ q ∧ q ≤ n) ∧
    (∀ (r : ℕ) (p q : ℤ), (p < 0 ∨ q < a) →
      IsZero (((hypercohomologyCouple
        (hypercohomologySecondFunctor f' g') K).pageCouple r).E p q)) ∧
    (∀ (r : ℕ) (n p q : ℤ), p + q = n →
      ¬ IsZero (((hypercohomologyCouple
        (hypercohomologySecondFunctor f' g') K).pageCouple r).E p q) →
      a ≤ q ∧ q ≤ n) ∧
    (∃ Z₁ : (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).LimitSubobjects,
      ∃ A₁ : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).AlphaColimit n,
      ∃ hA₁ : ∀ n : ℤ, (A₁ n).obj =
        (DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj)),
      ∃ hD₁ : ∀ n p : ℤ,
        (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).D p (n - p) =
          (DerivedCategory.homologyFunctor
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K (n - p)).obj)),
      (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).ConvergesTo Z₁ A₁ ∧
      (∀ n p : ℤ, (A₁ n).ι p ≫ eqToHom (hA₁ n) =
        eqToHom (hD₁ n p) ≫
          hypercohomologyAbutmentMap (hypercohomologyFirstFunctor f) K n (n - p)) ∧
      (∀ n : ℤ,
        ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).imageFiltration n
          (A₁ n)).IsFinite) ∧
      (∀ n p : ℤ,
        (Subobject.«exists» (eqToHom (hA₁ n))).obj
          (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).imageFiltration n
            (A₁ n)).step p) =
          imageSubobject
            (hypercohomologyAbutmentMap (hypercohomologyFirstFunctor f) K n (n - p)))) ∧
    (∃ Z₂ : (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).LimitSubobjects,
      ∃ A₂ : ∀ n : ℤ,
        (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).AlphaColimit n,
      ∃ hA₂ : ∀ n : ℤ, (A₂ n).obj =
        (DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj K.obj)),
      ∃ hD₂ : ∀ n p : ℤ,
        (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).D p (n - p) =
          (DerivedCategory.homologyFunctor
            (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
            ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K (n - p)).obj)),
      (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).ConvergesTo Z₂ A₂ ∧
      (∀ n p : ℤ, (A₂ n).ι p ≫ eqToHom (hA₂ n) =
        eqToHom (hD₂ n p) ≫
          hypercohomologyAbutmentMap (hypercohomologySecondFunctor f' g') K n (n - p)) ∧
      (∀ n : ℤ,
        ((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).imageFiltration n
          (A₂ n)).IsFinite) ∧
      (∀ n p : ℤ,
        (Subobject.«exists» (eqToHom (hA₂ n))).obj
          (((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).imageFiltration n
            (A₂ n)).step p) =
          imageSubobject
            (hypercohomologyAbutmentMap (hypercohomologySecondFunctor f' g') K n (n - p)))) := by
  sorry

end AlgebraicGeometry.Etale
