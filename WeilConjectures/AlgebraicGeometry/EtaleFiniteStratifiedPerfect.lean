/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification

/-! # Finite stratified-perfect complexes on the ordinary etale site

Source: Bhatt--Scholze, Definition 6.3.1, pp. 45--46
(blueprint: def-per-etale-finite-stratified-perfect).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- A finite constructible locally closed stratification on which the restrictions
are etale locally constant perfect coefficient complexes. No uniform bounds on the
cover members are imposed in this definition.
Source: Bhatt--Scholze, Definition 6.3.1, p. 45
(blueprint: def-per-etale-finite-stratified-perfect). -/
def IsFiniteStratifiedPerfectEtaleComplex (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : ObjectProperty (DerivedCategoryModule A T) :=
  fun K ↦ ∃ S : Scheme.FiniteLocallyClosedStratification T,
    (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
    ∀ i : Fin S.n, IsLocallyConstantPerfectEtaleComplex A (S.domain i)
      ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).mapDerivedCategory.obj K)

end AlgebraicGeometry.Etale
