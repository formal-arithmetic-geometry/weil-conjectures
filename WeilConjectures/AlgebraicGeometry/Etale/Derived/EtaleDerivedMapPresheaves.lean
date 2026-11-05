/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Presheaves of derived etale maps

Source: Stacks Project, sites-cohomology.tex, Tag 09BE, lemma-locally-constant-map,
and the derived Hom presheaf used in the finite-ring extension of that lemma
(blueprint: def-weil-pbc-etale-derived-map-presheaves).
-/

@[expose] public section

universe u u'

open CategoryTheory Opposite

open CategoryTheory.Limits

section ExactFunctors

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

end ExactFunctors

section ExactAssociativity

variable {C₀ C₁ C₂ C₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  (H : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (F : C₂ ⥤ C₃)
  (GH : C₀ ⥤ C₂) (FG : C₁ ⥤ C₃) (FGH : C₀ ⥤ C₃)
  [H.Additive] [G.Additive] [F.Additive] [GH.Additive] [FG.Additive] [FGH.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
  [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]

end ExactAssociativity

section ExactIdentity

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) (J : D ⥤ D)
  [F.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]

end ExactIdentity

namespace AlgebraicGeometry.Etale

variable {X : Scheme.{u}} (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] upperStar upperStarComp upperStarId

section PullbackCoherence

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

end PullbackCoherence

end AlgebraicGeometry.Etale
