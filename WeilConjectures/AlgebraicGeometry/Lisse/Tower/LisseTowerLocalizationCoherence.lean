/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizationTransport
public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPullbackCompositionScalar
public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantComplexPresentation
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentationPaste
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantComplexPresentation

/-! # The localized inverse image through the fixed realization

The inverse image `lisseTowerLocalizationPull` along `a` followed by `b` is identified
with the ringed inverse images along `b` and `a`, compatibly with the scalar faces. The
ringed inverse images compose to the ringed inverse image along the composite,
compatibly with the restriction/pullback comparisons.

Source: Stacks Project, Modules on Sites, Tags 03CY, 03D2, 03D3 and 03DA;
Cohomology on Sites, Tag 0D6D.
-/

public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor

namespace LisseTowerLocalizationTransport

end LisseTowerLocalizationTransport

open LisseTowerLocalizationTransport

namespace AlgebraicGeometry.Scheme

section Chain

variable {X Z S T : Scheme.{u}} (t : Z ⟶ X) (b : S ⟶ Z) (a : T ⟶ S)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (j n : ℕ)

end Chain
section Represents

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end Represents
section Ordinary

variable {X Z S T : Scheme.{u}} (t : Z ⟶ X) (b : S ⟶ Z) (a : T ⟶ S)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

end Ordinary
section Derived

variable {X Z S T : Scheme.{u}} (t : Z ⟶ X) (b : S ⟶ Z) (a : T ⟶ S)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end Derived
section Scalar

variable {X Z S T : Scheme.{u}} (t : Z ⟶ X) (b : S ⟶ Z) (a : T ⟶ S)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end Scalar

end AlgebraicGeometry.Scheme
