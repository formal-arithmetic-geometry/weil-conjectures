/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# Coherence of the projection formula

Let `f : X ⟶ Y` admit a compactification. We record the coherence properties of the projection
transformation `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` of blueprint `sk-prop-sf-pf-coherence`
(detailed node `prop-sf-pf-coherence`) as identities between morphisms:

- naturality in `K` and `L`
  (`AlgebraicGeometry.Etale.projectionMapOfCompactification_naturality`): `PF` is a natural
  transformation of bifunctors;
- the identity case (`AlgebraicGeometry.Etale.hasProjectionFormula_id`);
- independence of the compactification: the comparison isomorphisms `Rf_!(c) ≅ Rf_!` intertwine
  the projection maps
  (`AlgebraicGeometry.Etale.projectionMapOfCompactification_rightDerivedLowerShriekIso`,
  and, along a refinement and for any coefficients,
  `AlgebraicGeometry.Etale.projectionMapOfCompactification_comparison`);
- for proper `f`, agreement with the direct-image projection formula through `Rf_! ≅ Rf_*`
  (`AlgebraicGeometry.Etale.projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar`);
- compatibility with base change
  (`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`);
- associativity with respect to the derived tensor product
  (`AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`), and, as its
  special case for the constant complex `(Λ/J)_Y`, compatibility with finite reduction
  `- ⊗ᴸ (Λ/J)` (`AlgebraicGeometry.Etale.projectionMapOfCompactification_reductionModIdeal`).

## Implementation notes

Finite reduction is modelled in this repository, as in
`AlgebraicGeometry.Etale.reductionModIdeal`, by the endofunctor `K ↦ K ⊗ᴸ (Λ/J)_X` of `D(X_ét, Λ)`;
its compatibility with `Rf_!` is the projection map at `L = (Λ/J)_Y`
(`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_finite`), so
the reduction square of the projection map is the associativity of the projection map.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula; agreement with the
direct-image projection formula for proper `f`. For a proper `f`, the identification
`Rf_! ≅ Rf_*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`)
intertwines the projection map `PF` of `Rf_!` with the projection map
`Rf_*K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^*L)` of the direct image:
```
Rf_!K ⊗ᴸ L ──PF──▶ Rf_!(K ⊗ᴸ Lf^*L)
    │ ≅                  │ ≅
    ▼                    ▼
Rf_*K ⊗ᴸ L ──PF_*──▶ Rf_*(K ⊗ᴸ Lf^*L)
``` -/
theorem projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar (f : X ⟶ Y)
    [IsProper f] (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMap A f).app K).app L ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom.app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) =
      ((-⊗ᴸ-(Y)[A]).map ((rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom.app K)).app L ≫
        ((rightDerivedLowerStarProjectionMap A f).app K).app L := by
  have h : (rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom =
      compactificationForgetSupports A (HasCompactification.compactification f) := by
    rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
      rightDerivedLowerShriekToLowerStarComp_comp_eq]
    rfl
  rw [h]
  exact projectionMapOfCompactification_comp_compactificationForgetSupports A _ K L

end General

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

set_option hygiene false in
/-- The constant complex `(Λ/J)_Y` placed in degree zero, by which `reductionModIdeal` tensors. -/
local notation "𝐏(" Y ", " J ")" =>
  constantSingle (ModuleCat.{u + 1} Λ) Y (ModuleCat.of Λ (Λ ⧸ J))

section Reduction

-- The generic associativity `AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`
-- braids `ModuleCat Λ` through its symmetric structure and étale sheaves through
-- `Etale.sheafBraidedCategory`; use the same instances here so that the specialisation below
-- matches it syntactically rather than up to an expensive unfolding.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

end Reduction

variable [Finite Λ]

/-- Blueprint `sk-prop-sf-pf-coherence`: Coherence of the projection formula; independence of the
compactification. For torsion coefficients and a quasi-compact `f`, the comparison isomorphism
`Rf_!(c) ≅ Rf_!` between the compactly supported direct images computed with a compactification
`c` and with the chosen one (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`) intertwines the
projection maps:
```
Rf_!(c)K ⊗ᴸ L ──PF_c──▶ Rf_!(c)(K ⊗ᴸ Lf^*L)
     │ ≅                      │ ≅
     ▼                        ▼
 Rf_!K ⊗ᴸ L   ──PF──▶   Rf_!(K ⊗ᴸ Lf^*L)
``` -/
theorem projectionMapOfCompactification_rightDerivedLowerShriekIso [QuasiCompact f]
    [HasCompactification f] (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app L ≫
        (rightDerivedLowerShriekIso Λ c).hom.app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj L)) =
      ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map ((rightDerivedLowerShriekIso Λ c).hom.app K)).app L ≫
        ((projectionMap _ f).app K).app L :=
  projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso Λ c _ K L

end Torsion

end Etale

end AlgebraicGeometry
