/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic

/-! # Strict scalar cone augmentations

Source: Stacks Project, sites-cohomology.tex, principal quotient formulas, Tag 06YP.
(blueprint: lem-cbc-regular-quotient-cone-chain).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v r
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Sheaf J CommRingCat.{r}}
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
  (T : CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ)
  (ρ : 𝟭 (CochainComplex (Modules R) ℤ) ⟶ T)
  (hz : ∀ P, (complexScalar R t).app P ≫ ρ.app P = 0)

variable {S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  (E : Modules R ⥤ Modules S) [E.Additive] (adj : E ⊣ restriction φ)

end SheafOfModules.RegularQuotientCone
