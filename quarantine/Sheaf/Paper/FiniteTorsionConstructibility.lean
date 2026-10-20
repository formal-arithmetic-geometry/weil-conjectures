/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated

/-!
# Finite-torsion constructible complexes on the pro-etale site

Source: Weil conjectures blueprint,
`literature/blueprint/master/blueprint/sec-smooth-purity/`
`sk-def-sf-operations/def-weil-finite-torsion-constructibility.md`,
node order 1454 (blueprint: def-weil-finite-torsion-constructibility).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The bounded constructible finite-torsion subcategory of the derived category of
sheaves of `A_{E,n}`-modules on the small pro-etale site of `Y`.

Source: Weil conjectures blueprint, node `def-weil-finite-torsion-constructibility`,
order 1454 (blueprint: def-weil-finite-torsion-constructibility). The predicate is
finite support of cohomology degrees and constructibility of every cohomology sheaf;
the cited triangulated-closure theorem supplies the full triangulated structure.
-/
noncomputable def finiteTorsionConstructible
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    (Y : Scheme.{u}) : ObjectProperty (proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l E n)) :=
  letI := Padic.finite_coefficientExtensionRing l E n _hn
  fun K ↦
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) i).obj K)} ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y
        (Padic.coefficientExtensionRing l E n)
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules Y
            (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) i).obj K)

/-- The full category selected by `finiteTorsionConstructible`.
Source: Weil blueprint, node order 1454
(blueprint: def-weil-finite-torsion-constructibility). -/
noncomputable abbrev finiteTorsionConstructibleCategory
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :=
  (finiteTorsionConstructible D l hl E n hn Y).FullSubcategory

/-- The finite-torsion predicate is closed under isomorphisms.
Source: Weil blueprint, node order 1454
(blueprint: def-weil-finite-torsion-constructibility). -/
noncomputable instance finiteTorsionConstructible_isClosedUnderIsomorphisms
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    (finiteTorsionConstructible D l hl E n hn Y).IsClosedUnderIsomorphisms :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (proEtale_bounded_constructible_isTriangulated Y
    (Padic.coefficientExtensionRing l E n)).1

/-- The finite-torsion predicate is triangulated, by the recorded closure theorem.
Source: Weil blueprint, node order 1454
(blueprint: def-weil-finite-torsion-constructibility). -/
noncomputable instance finiteTorsionConstructible_isTriangulated
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    (finiteTorsionConstructible D l hl E n hn Y).IsTriangulated :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (proEtale_bounded_constructible_isTriangulated Y
    (Padic.coefficientExtensionRing l E n)).2

end AlgebraicGeometry.Scheme
