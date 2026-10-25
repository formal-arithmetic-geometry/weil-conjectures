/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# Compatibility of `Rf_!` and `Rf^!` with the extension of scalars `𝒪_E ⟶ E`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `k`
a field of characteristic `p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write
`T_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧` for the extension of scalars `E_X ⊗ᴸ_{𝒪_{E,X}} -` on bounded
constructible complexes (`ProEtale.boundedConstructibleExtendScalars`). This file builds the
coefficient comparisons of blueprint `sk-prop-scalar-six` for `Rf_!` and `Rf^!` along `𝒪_E ⟶ E`,
in the same way as
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility` does for
`E ⟶ ℚ̄_ℓ`.

* **(Push)** `Rg_*^{𝒪_E} ⋙ T_Y ⟶ T_Z ⋙ Rg_*^E`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarExtendScalars`), the restriction of
  `ProEtale.CondensedRing.derivedPushHom`; it is an isomorphism by blueprint
  `det-prop-scalar-six-direct-image`
  (`ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarExtendScalars`).
* **(Shriek)** for an open immersion `j`: `j_!^{𝒪_E} ⋙ T_X ≅ T_U ⋙ j_!^E`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso`), and for
  every `f`: `Rf_!^{𝒪_E} ⋙ T_Y ≅ T_X ⋙ Rf_!^E`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekExtendScalarsIso`), composed from the
  two along the chosen compactification.
* **The exchange for `f^!`**: the mate `Rf^!_{𝒪_E} ⋙ T_X ⟶ T_Y ⋙ Rf^!_E` of the inverse of
  (Shriek) under the adjunctions `Rf_! ⊣ Rf^!`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekExtendScalars`).

## Inputs from `sec-six-functors-basics`

* `ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarExtendScalars`: blueprint
  `det-prop-scalar-six-direct-image`, (Push) is an isomorphism.
* `ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekExtendScalars`: blueprint
  `det-prop-scalar-six-exceptional`, the exchange for `f^!` is an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### Zero morphisms -/

section Zero

variable (X : Scheme.{u})

/-- The extension of scalars `T_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧` preserves zero morphisms, as the
derived extension of scalars, a left adjoint, does. -/
instance : (boundedConstructibleExtendScalars X ℓ E).PreservesZeroMorphisms where
  map_zero A B := (boundedConstructible _).ι.map_injective (by
    have := (Mod.derivedExtendMapDerivedCategoryAdjunction
      (padicIntegersToPadicSubfield X ℓ E)).isLeftAdjoint
    have := Functor.preservesZeroMorphisms_of_isLeftAdjoint
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor
    have h := (boundedConstructibleExtendScalarsCompatibility X ℓ E).hom.naturality (0 : A ⟶ B)
    simp only [Functor.comp_map, Functor.map_zero, Limits.comp_zero] at h
    rw [(boundedConstructible _).ι.map_zero]
    exact (cancel_mono _).1 (h.trans (Limits.zero_comp).symm))

end Zero

/-! ### (Push) -/

section LowerStar

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y)

/-- **(Push)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E`: the canonical
comparison `Rg_*^{𝒪_E} ⋙ T_Y ⟶ T_Z ⋙ Rg_*^E`, the restriction of
`ProEtale.CondensedRing.derivedPushHom` along the fully faithful inclusions. -/
noncomputable def boundedConstructibleLowerStarExtendScalars :
    boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ g ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ⟶
      boundedConstructibleExtendScalars Z.left ℓ E ⋙
        boundedConstructibleLowerStar (Profinite.continuousMapRingObj E.1) ℓ g :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimage
    ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (boundedConstructibleExtendScalarsCompatibility Y.left ℓ E).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (boundedConstructibleLowerStarCompatibility _ ℓ g).hom _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _
        (derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) g.left) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (boundedConstructibleExtendScalarsCompatibility Z.left ℓ E).inv _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (boundedConstructibleLowerStarCompatibility _ ℓ g).inv ≫
      (Functor.associator _ _ _).inv)

/-- Compatibility required from `sec-six-functors-basics` (to be proved there): blueprint
`det-prop-scalar-six-direct-image`, (1), for the coefficient map `𝒪_E ⟶ E`. The canonical
comparison `(Rg_* K)_E ⟶ Rg_*(K_E)` (**(Push)**,
`boundedConstructibleLowerStarExtendScalars`) is an isomorphism for every bounded constructible
`𝒪_E`-complex `K` (here `Dctf(-, 𝒪_E) = Dᵇc(-, 𝒪_E)`). -/
instance isIso_boundedConstructibleLowerStarExtendScalars :
    IsIso (boundedConstructibleLowerStarExtendScalars ℓ E g) :=
  sorry

/-- **(Push)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E`, as an
isomorphism `Rg_*^{𝒪_E} ⋙ T_Y ≅ T_Z ⋙ Rg_*^E`. -/
noncomputable def boundedConstructibleLowerStarExtendScalarsIso :
    boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ g ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ≅
      boundedConstructibleExtendScalars Z.left ℓ E ⋙
        boundedConstructibleLowerStar (Profinite.continuousMapRingObj E.1) ℓ g :=
  asIso (boundedConstructibleLowerStarExtendScalars ℓ E g)

end LowerStar

/-! ### (Shriek) for an open immersion -/

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- **(Shriek)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E` and an open
immersion `j`: `j_!^{𝒪_E} ⋙ T_X ≅ T_U ⋙ j_!^E`, the restriction of
`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E.1) ℓ j ⋙
        boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars U.left ℓ E ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E.1) ℓ j :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleExtendScalarsCompatibility X.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedOpenImmersionShriekIso (padicIntegersRingObjToContinuousMapRingObj ℓ E) j.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleExtendScalarsCompatibility U.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j).symm ≪≫
      (Functor.associator _ _ _).symm)

end OpenImmersion

/-! ### (Shriek) and the exchange for `f^!` -/

section Shriek

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **(Shriek)** on bounded constructible complexes along a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, for the inclusion `𝒪_E ⟶ E`:
`Rf_!(c)^{𝒪_E} ⋙ T_Y ≅ T_X ⋙ Rf_!(c)^E`, composed of (Shriek) for the open immersion `i` and
(Push) for `g`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationExtendScalarsIso
    {f : X ⟶ Y} (c : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactification (Profinite.padicIntegersRingObj ℓ E.1) ℓ c ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        boundedConstructibleLowerShriekOfCompactification (Profinite.continuousMapRingObj E.1) ℓ
          c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarExtendScalarsIso ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso ℓ E c.overI) _ ≪≫
    Functor.associator _ _ _

variable (f : X ⟶ Y)

/-- **(Shriek)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E`:
`Rf_!^{𝒪_E} ⋙ T_Y ≅ T_X ⋙ Rf_!^E`, along the chosen compactification. -/
noncomputable def boundedConstructibleLowerShriekExtendScalarsIso :
    boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E.1) ℓ f ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ≅
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E.1) ℓ f :=
  boundedConstructibleLowerShriekOfCompactificationExtendScalarsIso ℓ E
    (compactificationOverField f)

/-- **The exchange for `f^!`**, for the inclusion `𝒪_E ⟶ E`: the canonical natural transformation
`Rf^!_{𝒪_E} ⋙ T_X ⟶ T_Y ⋙ Rf^!_E`, the mate of the inverse of (Shriek)
(`boundedConstructibleLowerShriekExtendScalarsIso`) under the adjunctions `Rf_! ⊣ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekExtendScalars :
    boundedConstructibleUpperShriek (Profinite.padicIntegersRingObj ℓ E.1) ℓ f ⋙
        boundedConstructibleExtendScalars X.left ℓ E ⟶
      boundedConstructibleExtendScalars Y.left ℓ E ⋙
        boundedConstructibleUpperShriek (Profinite.continuousMapRingObj E.1) ℓ f :=
  mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).inv

/-- The exchange for `f^!` as the mate of a two-square. -/
lemma boundedConstructibleUpperShriekExtendScalars_eq_mateEquiv :
    boundedConstructibleUpperShriekExtendScalars ℓ E f =
      (mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ f)
        (boundedConstructibleUpperShriekAdjunction _ ℓ f)
        (TwoSquare.mk _ _ _ _
          (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).inv)).natTrans :=
  rfl

/-- Compatibility required from `sec-six-functors-basics` (to be proved there): blueprint
`det-prop-scalar-six-exceptional` (`sk-prop-scalar-six`), the clause on `f^!` for the coefficient
change `𝒪_E ⟶ E`. The canonical comparison `Rf^!_{𝒪_E} ⋙ T_X ⟶ T_Y ⋙ Rf^!_E` (the mate of the
lower-shriek comparison) is an isomorphism on bounded constructible complexes. -/
theorem isIso_boundedConstructibleUpperShriekExtendScalars :
    IsIso (boundedConstructibleUpperShriekExtendScalars ℓ E f) :=
  sorry

end Shriek

end AlgebraicGeometry.ProEtale.CondensedRing
