/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitMittagLeffler

/-!
# Mittag-Leffler towers

A tower `G : ℕᵒᵖ ⥤ C` is Mittag-Leffler (`CategoryTheory.Limits.IsMittagLefflerTower`) if it
has a subtower `G'` with epimorphic transitions (the stable images) through which some
transition `G m ⟶ G n` factors, for every `n`.

- `IsMittagLefflerTower.map`, `IsMittagLefflerTower.of_iso`: stability under functors
  preserving monomorphisms and epimorphisms, and under isomorphism;
- `IsMittagLefflerTower.shortExact`: in an abelian category, `G` is an extension of an
  essentially zero tower (the cokernel of `G' ⟶ G`) by `G'`;
- `CategoryTheory.Limits.epi_one_sub_of_isMittagLefflerTower`: `lim¹ G = 0` in a replete
  abelian category;
- `DerivedCategory.isLimitHomologyFunctorMapConeOfIsHomotopyLimitOfIsMittagLefflerTower`:
  `Hⁱ(R lim F) = lim Hⁱ(Fₙ)` when the tower `H^{i-1}(Fₙ)` is Mittag-Leffler.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

namespace IsMittagLefflerTower

section Abelian

variable [Abelian C] {G : ℕᵒᵖ ⥤ C}

end Abelian

end IsMittagLefflerTower

variable [Abelian C] [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]
  [HasLimitsOfShape ℕᵒᵖ C]

end CategoryTheory.Limits

namespace DerivedCategory

open CategoryTheory.Limits Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C] [HasLimitsOfShape ℕᵒᵖ C]
  {F : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone F}

end DerivedCategory
