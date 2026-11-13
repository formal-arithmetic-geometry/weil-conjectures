/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.CategoryTheory.SiteCechMathlibComparison

/-!
# Comparison of the two étale Čech complex constructions

Source: Stacks Project, Cohomology on Sites, Tags 03AK and 03AM.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Chosen fibre products and the categorical products in the slice give isomorphic
Čech complexes, with their alternating restriction differentials.

Source: Stacks Project, Cohomology on Sites, Tags 03AK and 03AM, independence of the
choice of fibre products. -/
theorem nonempty_etale_siteCech_complex_iso
    (X : Scheme.{u}) (U : X.Etale) {J : Type (u + 1)}
    (V : J → X.Etale) (f : ∀ j : J, V j ⟶ U) (S : SiteCechComplex V f)
    (F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Nonempty (S.complex F ≅
      (cechComplexFunctor fun j : J ↦ Over.mk (f j)).obj ((Over.forget U).op ⋙ F)) := by
  exact CategoryTheory.SiteCechComplex.mathlib_complex_iso_exists (V := V) f S F

end AlgebraicGeometry.Scheme
