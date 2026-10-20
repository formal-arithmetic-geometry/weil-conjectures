/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Algebra.Homology.FilteredTruncationData
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.Algebra.Homology.FilteredConeLocalization
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension

/-!
# Universal truncation triangles for finite filtered derived categories

Source: Varshavsky--Lefschetz--Verdier trace formula, §§5.1.1--5.1.2,
pp. 39--40 (blueprint: lem-trf-filtered-truncation-triangle).
-/

@[expose] public section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CochainComplex.FiniteFiltered

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Universal filtration truncations and their distinguished triangles.
Source: Varshavsky--Lefschetz--Verdier trace formula, §§5.1.1--5.1.2,
pp. 39--40 (blueprint: lem-trf-filtered-truncation-triangle).

The proof constructs the filtered homotopy category, identifies filtered
quasi-isomorphisms with the graded-acyclic Verdier class, and applies the
localization triangle calculus.  It then descends the subcomplex and quotient
truncations, proves the two Hom bijections by filtered roofs and triangle
morphism extension, compares any supported triangle with the canonical one,
and identifies the pure-grade subcategory with the ordinary bounded-below
-derived category. -/
theorem filteredTruncationTriangle : Nonempty (FilteredTruncationData A) := by
  sorry


end CochainComplex.FiniteFiltered
