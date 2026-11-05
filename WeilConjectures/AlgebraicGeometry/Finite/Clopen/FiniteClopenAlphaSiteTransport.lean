/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateData
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
import WeilConjectures.CategoryTheory.RightDerivedPlusCube
import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenBetaSiteTransport
import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenTailSiteTransport

/-!
# Site comparison for the clopen alpha

Source: Stacks Project, Tags 099R, 09AF and 0F7B; steps 2--4 of
lem-cbc-finite-clopen-mate-site-transport
(blueprint: lem-cbc-finite-clopen-alpha-site-transport).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Etale.ClopenMateNormalization

namespace ExactAlphaLocalization

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (G : A ⥤ B) (Q : B ⥤ D) (P : A ⥤ C) (H : C ⥤ D)
  [G.Additive] [Q.Additive] [P.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

variable [EnoughInjectives A] [EnoughInjectives C]

section Cube

variable {B' C' A₀ B₀ B₀' C₀' : Type*}
  [Category* B'] [Category* C'] [Category* A₀] [Category* B₀]
  [Category* B₀'] [Category* C₀']
  [Abelian B'] [Abelian C'] [Abelian A₀] [Abelian B₀]
  [Abelian B₀'] [Abelian C₀']
  [HasDerivedCategory B'] [HasDerivedCategory C']
  [HasDerivedCategory A₀] [HasDerivedCategory B₀]
  [HasDerivedCategory B₀'] [HasDerivedCategory C₀']
  [EnoughInjectives B'] [EnoughInjectives A₀] [EnoughInjectives B₀']
  (G₁ : A ⥤ B) (H₁ : B' ⥤ C') (G₀ : A₀ ⥤ B₀) (H₀ : B₀' ⥤ C₀')
  (P₁ : A ⥤ B') (Q₁ : B ⥤ C') (P₀ : A₀ ⥤ B₀') (Q₀ : B₀ ⥤ C₀')
  (U : A ⥤ A₀) (V : B ⥤ B₀) (U' : B' ⥤ B₀') (V' : C' ⥤ C₀')
  [G₁.Additive] [H₁.Additive] [G₀.Additive] [H₀.Additive]
  [P₁.Additive] [Q₁.Additive] [P₀.Additive] [Q₀.Additive]
  [U.Additive] [V.Additive] [U'.Additive] [V'.Additive]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]
  [PreservesFiniteLimits H₀] [PreservesFiniteColimits H₀]
  [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits Q₁] [PreservesFiniteColimits Q₁]
  [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
  [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
  [PreservesFiniteLimits V'] [PreservesFiniteColimits V']

end Cube

end ExactAlphaLocalization

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
