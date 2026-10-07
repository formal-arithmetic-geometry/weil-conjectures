/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs

/-!
# Pullback of the constant `ℓ`-adic sheaf

The pullback of the constant `ℓ`-adic sheaf `ℚ̄_ℓ,V` along a morphism of schemes `g : W ⟶ V` is
the constant `ℓ`-adic sheaf `ℚ̄_ℓ,W` (Bhatt–Scholze, *The pro-étale topology for schemes*,
Lemma 4.2.12 and §6.8).

For a weakly étale `g` the pullback is restriction along the localization functor
`W.ProEt ⥤ V.ProEt` (`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), and
both sheaves have the locally finite continuous functions on `T` as sections over `T → W`.

For a general `g` this is stated here with `sorry`. The proof of Bhatt–Scholze shows that the
canonical map `g^* ℚ̄_ℓ,V ⟶ ℚ̄_ℓ,W` is an isomorphism using the constant profinite schemes
`V × K`, for `K` a compact subset of a finite-dimensional `ℚ_ℓ`-subspace of `ℚ̄_ℓ`, which are
weakly étale over `V` and represent continuous maps to `K`: every section of `ℚ̄_ℓ,W` is locally
the pullback of the tautological function on some `V × K`, and a section of `ℚ̄_ℓ,V` vanishing
on the image of a map factors through its zero locus, a weakly étale `V`-scheme.

## Main definitions

- `AlgebraicGeometry.ProEtale.upperStarAdicConstantSheafIsoOfWeaklyEtale`: `g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W`
  for a weakly étale `g`.

## Main results

- `AlgebraicGeometry.ProEtale.nonempty_upperStar_adicConstantSheaf_iso`: `g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W`
  for an arbitrary `g` (stated with `sorry`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {V W : Scheme.{u}}

/-- The restriction of the constant `ℓ`-adic sheaf along a weakly étale `g : W ⟶ V` is the
constant `ℓ`-adic sheaf: both have the locally finite continuous functions on `T` as sections
over `T → W`. -/
noncomputable def adicConstantSheafLocalizationRestrictionIso (g : W ⟶ V) (h : WeaklyEtale g) :
    (localizationRestriction (WeilCoefficients.{u} l) g h).obj (adicConstantSheaf l V) ≅
      adicConstantSheaf l W :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _)

/-- The pullback of the constant `ℓ`-adic sheaf along a weakly étale `g : W ⟶ V` is the constant
`ℓ`-adic sheaf, the pullback being restriction in this case. -/
noncomputable def upperStarAdicConstantSheafIsoOfWeaklyEtale (g : W ⟶ V) [h : WeaklyEtale g] :
    (g)^*[WeilCoefficients.{u} l].obj (adicConstantSheaf l V) ≅ adicConstantSheaf l W :=
  (upperStarIsoLocalizationRestriction _ g h).app _ ≪≫
    adicConstantSheafLocalizationRestrictionIso l g h

/-- **The pullback of the constant `ℓ`-adic sheaf is the constant `ℓ`-adic sheaf**
(Bhatt–Scholze, Lemma 4.2.12): for an arbitrary morphism `g : W ⟶ V`, `g^* ℚ̄_ℓ,V ≅ ℚ̄_ℓ,W`. The
sections of `ℚ̄_ℓ,W` are locally pulled back from the constant profinite schemes `V × K`, which
are weakly étale over `V`, and the relations between them come from zero loci of sections of
`ℚ̄_ℓ,V`, which are weakly étale over `V` as well. -/
theorem nonempty_upperStar_adicConstantSheaf_iso (g : W ⟶ V) :
    Nonempty ((g)^*[WeilCoefficients.{u} l].obj (adicConstantSheaf l V) ≅
      adicConstantSheaf l W) :=
  sorry

end AlgebraicGeometry.ProEtale
