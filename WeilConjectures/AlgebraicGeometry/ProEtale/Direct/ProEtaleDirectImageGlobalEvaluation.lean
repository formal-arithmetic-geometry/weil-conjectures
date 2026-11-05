/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleUnitLerayChainFormula
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackIdentity
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleUnitLerayChainFormula
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleComparisonLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate

/-!
# Normalized derived global sections after ordinary pro-etale direct image

Source: Stacks Project, sites-cohomology.tex, Tags 0D6H and 0D6E;
K-injective normalization and open-unit calculation in derived.tex, Tags 070Y and 0DVC
(blueprint: lem-pur-proetale-direct-image-global-evaluation).

The section functor and its terminal-object comparison are the published ordinary
constant-ring constructions. All derived images below are the actual finite-level
sectionwise direct image, without completion or a constructibility restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
section
attribute [-instance]
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

section MateTransport
variable {C D E : Type*} [Category C] [Category D] [Category E]
  {Lf : D ⥤ C} {Lg : E ⥤ D} {Lc : E ⥤ C}
  {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : C ⥤ E}
  (af : Lf ⊣ F) (ag : Lg ⊣ G) (ac : Lc ⊣ H)
  (ef : F ≅ F') (eg : G ≅ G') (ec : H ≅ H')
  (a : Lc ⟶ Lg ⋙ Lf)

end MateTransport

attribute [local irreducible] proEtaleUnitLerayDirectImageIso

section SectionRealization
variable (A : Type u) [CommRing A] [Finite A]

end SectionRealization

-- The coefficient transports require comparing nested pushforward module actions.
variable (P : WeilConjectures.PurityFiniteSetting.{u})
  {T Y W : Scheme.{u}}
  [T.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [W.Over (Spec (.of P.field.k))]

end AlgebraicGeometry.Scheme

end
