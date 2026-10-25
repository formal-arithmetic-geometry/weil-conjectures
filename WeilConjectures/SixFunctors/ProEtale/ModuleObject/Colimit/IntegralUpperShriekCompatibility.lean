/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility

/-!

# Compatibility of `Rf^!` with the extension of scalars `𝒪_E ⟶ E`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`k` a field of characteristic `p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write
`T_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧` for the extension of scalars `E_X ⊗ᴸ_{𝒪_{E,X}} -` on bounded
constructible complexes (`ProEtale.boundedConstructibleExtendScalars`). This file treats the
clause on `f^!` of blueprint `det-prop-scalar-six-exceptional` for the coefficient change
`𝒪_E ⟶ E`, mirroring the treatment of `E ⟶ ℚ̄_ℓ` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility`.

* **(Pull)** on bounded constructible complexes: `Lf^*_{𝒪_E} ⋙ T_X ≅ T_Y ⋙ Lf^*_E`
  (`ProEtale.CondensedRing.boundedConstructibleUpperStarExtendScalarsIso`, proved using the
  flatness of `E_X` over `𝒪_{E,X}`).
* **(Push)** for any `g`: the canonical comparison `Rg_*^{𝒪_E} ⋙ T_Y ⟶ T_Z ⋙ Rg_*^E`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarExtendScalars`), the restriction of
  `ProEtale.CondensedRing.derivedPushHom`, and the resulting isomorphism
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarExtendScalarsIso`).
* **(Shriek)** for an open immersion `j`: `j_!^{𝒪_E} ⋙ T_X ≅ T_U ⋙ j_!^E`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso`), and
  for every `f`: `Rf_!^{𝒪_E} ⋙ T_Y ≅ T_X ⋙ Rf_!^E`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekExtendScalarsIso`), composed from the
  two along the chosen compactification.
* **The exchange for `f^!`**: the mate `Rf^!_{𝒪_E} ⋙ T_X ⟶ T_Y ⋙ Rf^!_E` of the inverse of
  (Shriek) under the adjunctions `Rf_! ⊣ Rf^!`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekExtendScalars`). For an open immersion
  `j` the exchange `j^*_{𝒪_E} ⋙ T_U ⟶ T_X ⋙ j^*_E` is an isomorphism
  (`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionUpperStarExtendScalars`), `j_!`
  being fully faithful and `j^*` commuting with `T` by (Pull). The exchange for `f^!` is the
  horizontal composite of the exchanges for the open and the proper part of the compactification
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactificationExtendScalars_eq`).

## Compatibilities required from other sections

* `ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarExtendScalars`: blueprint
  `det-prop-scalar-six-direct-image` (1), the comparison for `Rg_*` is an isomorphism on bounded
  constructible complexes.
* `ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekExtendScalars`: blueprint
  `det-prop-scalar-six-exceptional`, the exchange for `Rf^!` is an isomorphism on bounded
  constructible complexes.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

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
`det-prop-scalar-six-direct-image` (1), for the listed coefficient map `𝒪_E ⟶ E`. For every
morphism `g` and every bounded constructible `K`, the comparison
`γ_{g,K} : (Rg_*K)_E ⟶ Rg_*(K_E)` is an isomorphism. The canonical map
`boundedConstructibleLowerStarExtendScalars` is the mate of the restriction-of-scalars comparison
`ProEtale.CondensedRing.derivedComapLowerStarIso`, which is `γ`. -/
theorem isIso_boundedConstructibleLowerStarExtendScalars :
    IsIso (boundedConstructibleLowerStarExtendScalars ℓ E g) :=
  sorry

/-- **(Push)** on bounded constructible complexes, for the inclusion `𝒪_E ⟶ E`:
`Rg_*^{𝒪_E} ⋙ T_Y ≅ T_Z ⋙ Rg_*^E`, the canonical comparison
`boundedConstructibleLowerStarExtendScalars`, an isomorphism by
`isIso_boundedConstructibleLowerStarExtendScalars`. -/
noncomputable def boundedConstructibleLowerStarExtendScalarsIso :
    boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ g ⋙
        boundedConstructibleExtendScalars Y.left ℓ E ≅
      boundedConstructibleExtendScalars Z.left ℓ E ⋙
        boundedConstructibleLowerStar (Profinite.continuousMapRingObj E.1) ℓ g :=
  haveI := isIso_boundedConstructibleLowerStarExtendScalars ℓ E g
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

/-- The exchange `j^*_{𝒪_E} ⋙ T_U ⟶ T_X ⋙ j^*_E` for an open immersion `j`: the mate of the
inverse of (Shriek) under the adjunctions `j_! ⊣ j^*`. -/
noncomputable def boundedConstructibleOpenImmersionUpperStarExtendScalars :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ j ⋙
        boundedConstructibleExtendScalars U.left ℓ E ⟶
      boundedConstructibleExtendScalars X.left ℓ E ⋙
        boundedConstructibleUpperStar (Profinite.continuousMapRingObj E.1) ℓ j :=
  mateEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso ℓ E j).inv

/-- The exchange for an open immersion `j` is an isomorphism: `j_!` is fully faithful on both
sides, and `j^*` commutes with the extension of scalars by (Pull)
(`boundedConstructibleUpperStarExtendScalarsIso`). -/
instance isIso_boundedConstructibleOpenImmersionUpperStarExtendScalars :
    IsIso (boundedConstructibleOpenImmersionUpperStarExtendScalars ℓ E j) :=
  isIso_mateEquiv_of_isIso_unit _ _ _ (boundedConstructibleUpperStarExtendScalarsIso ℓ E j).symm

end OpenImmersion

/-! ### (Shriek) and the exchange for `f^!` -/

section Shriek

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- **(Shriek)** on bounded constructible complexes along a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, for the inclusion `𝒪_E ⟶ E`:
`Rf_!(c)^{𝒪_E} ⋙ T_Y ≅ T_X ⋙ Rf_!(c)^E`, composed of (Shriek) for the open immersion `i` and
(Push) for the proper `g`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationExtendScalarsIso :
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

/-- The exchange `Rg^!_{𝒪_E} ⋙ T_Z ⟶ T_Y ⋙ Rg^!_E` for the proper part `g` of a
compactification: the mate of the inverse of (Push) under the adjunctions `Rg_* ⊣ Rg^!`. -/
noncomputable def boundedConstructibleProperUpperShriekExtendScalars :
    (boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ c.overG).rightAdjoint ⋙
        boundedConstructibleExtendScalars c.overObj.left ℓ E ⟶
      boundedConstructibleExtendScalars Y.left ℓ E ⋙
        (boundedConstructibleLowerStar (Profinite.continuousMapRingObj E.1) ℓ
          c.overG).rightAdjoint :=
  mateEquiv (Adjunction.ofIsLeftAdjoint _) (Adjunction.ofIsLeftAdjoint _)
    (boundedConstructibleLowerStarExtendScalarsIso ℓ E c.overG).inv

/-- The exchange `Rf^!(c)_{𝒪_E} ⋙ T_X ⟶ T_Y ⋙ Rf^!(c)_E` along a compactification `c`: the mate
of the inverse of (Shriek) under the adjunctions `Rf_!(c) ⊣ Rf^!(c)`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationExtendScalars :
    boundedConstructibleUpperShriekOfCompactification (Profinite.padicIntegersRingObj ℓ E.1) ℓ c ⋙
        boundedConstructibleExtendScalars X.left ℓ E ⟶
      boundedConstructibleExtendScalars Y.left ℓ E ⋙
        boundedConstructibleUpperShriekOfCompactification (Profinite.continuousMapRingObj E.1) ℓ
          c :=
  mateEquiv (boundedConstructibleUpperShriekOfCompactificationAdjunction _ ℓ c)
    (boundedConstructibleUpperShriekOfCompactificationAdjunction _ ℓ c)
    (boundedConstructibleLowerShriekOfCompactificationExtendScalarsIso ℓ E c).inv

set_option maxHeartbeats 400000 in
-- `mateEquiv_hcomp` is matched against the unfolded adjunction `Rf_!(c) ⊣ Rf^!(c)`.
/-- The exchange for `f^!` along a compactification `c = (X ⟶[i] Z ⟶[g] Y)` is the horizontal
composite of the exchange for the proper part `g` and of the exchange for the open immersion `i`:
the mates of a vertical composite of squares are the horizontal composite of the mates
(`CategoryTheory.mateEquiv_hcomp`). -/
lemma boundedConstructibleUpperShriekOfCompactificationExtendScalars_eq :
    boundedConstructibleUpperShriekOfCompactificationExtendScalars ℓ E c =
      TwoSquare.hComp (boundedConstructibleProperUpperShriekExtendScalars ℓ E c)
        (boundedConstructibleOpenImmersionUpperStarExtendScalars ℓ E c.overI) := by
  have h : (boundedConstructibleLowerShriekOfCompactificationExtendScalarsIso ℓ E c).inv =
      TwoSquare.vComp
        (boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso ℓ E c.overI).inv
        (boundedConstructibleLowerStarExtendScalarsIso ℓ E c.overG).inv := by
    ext K
    simp [boundedConstructibleLowerShriekOfCompactificationExtendScalarsIso, TwoSquare.vComp]
  unfold boundedConstructibleUpperShriekOfCompactificationExtendScalars
  rw [h]
  exact mateEquiv_hcomp
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ c.overI)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ c.overI)
    (Adjunction.ofIsLeftAdjoint
      (boundedConstructibleLowerStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ c.overG))
    (Adjunction.ofIsLeftAdjoint
      (boundedConstructibleLowerStar (Profinite.continuousMapRingObj E.1) ℓ c.overG))
    (boundedConstructibleOpenImmersionLowerShriekExtendScalarsIso ℓ E c.overI).inv
    (boundedConstructibleLowerStarExtendScalarsIso ℓ E c.overG).inv

/-- The exchange for `f^!` along a compactification `c` is an isomorphism as soon as the exchange
for its proper part is one, the exchange for the open immersion being an isomorphism. -/
lemma isIso_boundedConstructibleUpperShriekOfCompactificationExtendScalars
    [IsIso (boundedConstructibleProperUpperShriekExtendScalars ℓ E c)] :
    IsIso (boundedConstructibleUpperShriekOfCompactificationExtendScalars ℓ E c) := by
  rw [boundedConstructibleUpperShriekOfCompactificationExtendScalars_eq]
  unfold TwoSquare.hComp
  infer_instance

end OfCompactification

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

/-- **The exchange for `f^!`**, for the inclusion `𝒪_E ⟶ E`: the canonical natural
transformation `Rf^!_{𝒪_E} ⋙ T_X ⟶ T_Y ⋙ Rf^!_E`, the mate of the inverse of (Shriek)
(`boundedConstructibleLowerShriekExtendScalarsIso`) under the adjunctions `Rf_! ⊣ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekExtendScalars :
    boundedConstructibleUpperShriek (Profinite.padicIntegersRingObj ℓ E.1) ℓ f ⋙
        boundedConstructibleExtendScalars X.left ℓ E ⟶
      boundedConstructibleExtendScalars Y.left ℓ E ⋙
        boundedConstructibleUpperShriek (Profinite.continuousMapRingObj E.1) ℓ f :=
  mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).inv

/-- The exchange for `f^!` is an isomorphism as soon as the exchange for the proper part of the
chosen compactification is one. -/
lemma isIso_boundedConstructibleUpperShriekExtendScalars_of_isIso
    [IsIso (boundedConstructibleProperUpperShriekExtendScalars ℓ E
      (compactificationOverField f))] :
    IsIso (boundedConstructibleUpperShriekExtendScalars ℓ E f) :=
  isIso_boundedConstructibleUpperShriekOfCompactificationExtendScalars ℓ E _

/-- Compatibility required from `sec-six-functors-basics` (to be proved there): blueprint
`det-prop-scalar-six-exceptional`, the clause on `f^!` for the coefficient change `𝒪_E ⟶ E`. The
canonical comparison `Rf^!_{𝒪_E} ⋙ T_X ⟶ T_Y ⋙ Rf^!_E` (the mate of the lower-shriek
comparison) is an isomorphism on bounded constructible complexes. Its open half is proved
(`isIso_boundedConstructibleOpenImmersionUpperStarExtendScalars`); the proper half is the content
of the node. -/
theorem isIso_boundedConstructibleUpperShriekExtendScalars :
    IsIso (boundedConstructibleUpperShriekExtendScalars ℓ E f) :=
  sorry

/-- The exchange for `f^!` as an isomorphism `Rf^!_{𝒪_E} ⋙ T_X ≅ T_Y ⋙ Rf^!_E`. -/
noncomputable def boundedConstructibleUpperShriekExtendScalarsIso :
    boundedConstructibleUpperShriek (Profinite.padicIntegersRingObj ℓ E.1) ℓ f ⋙
        boundedConstructibleExtendScalars X.left ℓ E ≅
      boundedConstructibleExtendScalars Y.left ℓ E ⋙
        boundedConstructibleUpperShriek (Profinite.continuousMapRingObj E.1) ℓ f :=
  haveI := isIso_boundedConstructibleUpperShriekExtendScalars ℓ E f
  asIso (boundedConstructibleUpperShriekExtendScalars ℓ E f)

end Shriek

end AlgebraicGeometry.ProEtale.CondensedRing
