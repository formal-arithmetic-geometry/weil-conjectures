/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage

/-!
# Intrinsic constructibility in the fixed-coefficient presentation

Source: blueprint, def-weil-proetale-constructible-sheaf, second paragraph
(blueprint: def-weil-proetale-constructible-sheaf).
This is the intrinsic finite-stratification definition in the fixed-module encoding
and in the coefficient universe required by the small pro-etale site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite constructible locally closed stratification, local constancy on each
stratum, and finite geometric stalks. No bound, common stratification, or etale
origin is part of this sheaf predicate. Source: blueprint,
def-weil-proetale-constructible-sheaf, second paragraph
(blueprint: def-weil-proetale-constructible-sheaf). -/
def IsConstructibleProEtaleFixedModuleSheaf (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) : Prop :=
  ∃ S : Stratification Y, 0 < S.n ∧
    (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
    ∀ i : Fin S.n,
      IsLocallyConstantProEtaleFixedModuleSheaf (S.domain i) A
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricFixedModuleStalk y A
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F))

end AlgebraicGeometry.Scheme
