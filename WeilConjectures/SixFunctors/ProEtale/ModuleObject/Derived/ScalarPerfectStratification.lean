/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction

/-! # Finite scalar-perfect stratifications -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- A finite constructible stratification on which the given complex is locally a bounded
complex of finite projective scalar modules.
Source: latest blueprint, internal-Hom stability, first proof paragraph
(blueprint: def-sfb-scalar-perfect-stratification). -/
def HasScalarPerfectStratification (X : Scheme.{u})
    (K : DerivedCategory (supportModules Λ X)) : Prop :=
  ∃ s : Scheme.Stratification X, ∀ a : Fin s.n,
    IsLocallyConstantPerfectComplex Λ (s.domain a)
      ((upperStar Λ (s.immersion a)).mapDerivedCategory.obj K)

end AlgebraicGeometry.ProEtale.CondensedRing
