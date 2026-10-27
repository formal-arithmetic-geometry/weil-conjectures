/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat

/-! # Flat homogeneous charts from a finite locally free graded tail

Source: Stacks Project, Algebra, Tags 00JM, 00CO and 05UT; the explicit tail-colimit
argument in the DAG (blueprint: lem-sfb-locally-free-tail-chart-flatness).

`RelativeProjAlgebra` records exactly the quasi-coherent graded algebra sheaf, its
homogeneous pieces, and their direct-sum identification. No relative Proj output is
required. We use its actual section ring and image grading on each affine open.
The base action on the chart ring is the existing `HomogeneousLocalization.algebra`,
`R → A_0 → A_(f),0`; it does not identify the degree-zero component with the base ring.
The universal property below is the definition of a colimit of modules, written as
compatible linear families so that the formula on arbitrary fractions is visible.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.RelativeProjAlgebra

/-- The inclusion of homogeneous sheaf sections into their image in the section algebra.
Source: Stacks, Algebra, Tag 00JM
(blueprint: lem-sfb-locally-free-tail-chart-flatness). -/
def tailChartSection {X : Scheme.{u}} (A : RelativeProjAlgebra X)
    (V : X.affineOpens) (d : ℕ) :
    Γ(A.piece d, V.1) →ₗ[Γ(X, V.1)] A.grade V d :=
  ((Sigma.ι A.piece d ≫ A.decomposition.hom).val.app (op V.1)).hom.rangeRestrict

/-- The degree-zero chart ring localized at a degree-one homogeneous section.
Source: Stacks, Algebra, Tag 00JM
(blueprint: lem-sfb-locally-free-tail-chart-flatness). -/
abbrev tailChartRing {X : Scheme.{u}} (A : RelativeProjAlgebra X)
    (V : X.affineOpens) (f : A.grade V 1) :=
  HomogeneousLocalization.Away (A.grade V) f.val

/-- The fraction a/f^d for an actual section of the d-th homogeneous sheaf.
Source: Stacks, Algebra, Tag 00JM
(blueprint: lem-sfb-locally-free-tail-chart-flatness). -/
def tailChartFraction {X : Scheme.{u}} (A : RelativeProjAlgebra X)
    (V : X.affineOpens) (f : A.grade V 1) (d : ℕ) (a : Γ(A.piece d, V.1)) :
    A.tailChartRing V f :=
  HomogeneousLocalization.Away.mk (A.grade V) f.property d (A.tailChartSection V d a).val
    (by
      rw [smul_eq_mul, mul_one]
      exact (A.tailChartSection V d a).property)

/-- A finite locally free graded tail gives finitely presented projective flat sections
and a flat degree-zero homogeneous chart, with its tail-colimit universal property.
Ranks and trivializing neighbourhoods may depend on both the point and the degree.

Source: Stacks Project, Algebra, Tags 00JM, 00CO and 05UT
(blueprint: lem-sfb-locally-free-tail-chart-flatness).

Proof:
1. For each d >= m separately apply finitePresentation_projective_sections
(lem-pc-finite-flat-affine-sections-projective). Projective implies flat by
Module.Flat.of_projective (lem-weil-pbc-projective-module-flat).
2. The degrees at least m form a small nonempty directed set, containing m and
with upper bounds given by maximum. Define t(d,e)(a) = f^(e-d)a and mu(d)(a) = a/f^d.
Bilinearity gives linear maps. Addition of exponents gives the diagram and cocone laws.
Every fraction a/f^e equals mu(D)(t(e,D)(a)) for D >= max(e,m).
3. For compatible h_d prescribe h(a/f^e) = h_D(f^(D-e)a). Compatibility makes
this independent of enlarging D. If a/f^e = b/f^t, the localization relation
(def-weil-ring-localization-away) gives k with f^k(f^t a - f^e b) = 0.
Choose L above m, the two chosen levels, and e+t+k. Multiplication by
f^(L-e-t-k) makes the two numerators equal in degree L, so their h_L-values agree.
There is no cancellation or regularity assumption on f.
4. A common large denominator proves additivity; scalar multiplication is
immediate from the structural base action. Taking D=d gives factorization.
Every fraction has such a representative, so factorization determines h uniquely.
This is the colimit universal property (def-weil-pbc-category-colimit).
5. Apply filteredColimit_flat (lem-weil-pbc-filtered-colimit-flat-modules) to
this tail diagram and the flat modules from step 1.
6. If f^N=0, the localization is zero and compatibility forces
h_d(a)=h_(d+N)(f^N a)=0. Thus the same construction includes nilpotent f, f=0,
the zero ring and empty affine opens. No Noetherian hypothesis is used. -/
theorem locallyFree_tail_chart_flatness {X : Scheme.{u}} (A : RelativeProjAlgebra X)
    (m : ℕ) (htail : ∀ d : ℕ, m ≤ d → (A.piece d).IsFiniteLocallyFree)
    (V : X.affineOpens) (f : A.grade V 1) :
    (∀ d : ℕ, m ≤ d →
      Module.FinitePresentation Γ(X, V.1) Γ(A.piece d, V.1) ∧
      Module.Projective Γ(X, V.1) Γ(A.piece d, V.1) ∧
      Module.Flat Γ(X, V.1) Γ(A.piece d, V.1)) ∧
    (∃ (t : ∀ (d e : ℕ), d ≤ e →
          Γ(A.piece d, V.1) →ₗ[Γ(X, V.1)] Γ(A.piece e, V.1))
        (μ : ∀ d : ℕ, Γ(A.piece d, V.1) →ₗ[Γ(X, V.1)] A.tailChartRing V f),
      (∀ (d e : ℕ) (hde : d ≤ e) (a : Γ(A.piece d, V.1)),
        (A.tailChartSection V e (t d e hde a)).val =
          f.val ^ (e - d) * (A.tailChartSection V d a).val) ∧
      (∀ (d : ℕ) (a : Γ(A.piece d, V.1)), μ d a = A.tailChartFraction V f d a) ∧
      (∀ (d : ℕ) (hd : m ≤ d), t d d le_rfl = LinearMap.id) ∧
      (∀ (d e k : ℕ) (hd : m ≤ d) (hde : d ≤ e) (hek : e ≤ k),
        (t e k hek).comp (t d e hde) = t d k (hde.trans hek)) ∧
      (∀ (d e : ℕ) (hd : m ≤ d) (hde : d ≤ e), (μ e).comp (t d e hde) = μ d) ∧
      (∀ (M : Type (max u v)) [AddCommGroup M] [Module Γ(X, V.1) M]
          (h : ∀ d : {d : ℕ // m ≤ d}, Γ(A.piece d.val, V.1) →ₗ[Γ(X, V.1)] M),
        (∀ (d e : {d : ℕ // m ≤ d}) (hde : d.val ≤ e.val),
          (h e).comp (t d.val e.val hde) = h d) →
        ∃ H : A.tailChartRing V f →ₗ[Γ(X, V.1)] M,
          (∀ d : {d : ℕ // m ≤ d}, H.comp (μ d.val) = h d) ∧
          (∀ H' : A.tailChartRing V f →ₗ[Γ(X, V.1)] M,
            (∀ d : {d : ℕ // m ≤ d}, H'.comp (μ d.val) = h d) → H' = H) ∧
          (∀ (e : ℕ) (a : Γ(A.piece e, V.1)) (D : ℕ) (heD : e ≤ D) (hmD : m ≤ D),
            H (A.tailChartFraction V f e a) = h ⟨D, hmD⟩ (t e D heD a)))) ∧
    Module.Flat Γ(X, V.1) (A.tailChartRing V f) := by
  sorry

end AlgebraicGeometry.RelativeProjAlgebra
