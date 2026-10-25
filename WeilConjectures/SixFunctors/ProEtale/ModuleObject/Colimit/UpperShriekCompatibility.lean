/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.MatesFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# Compatibility of `Rf^!` with the extension of scalars `E ⟶ ℚ̄_ℓ`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, and `k` a field of characteristic
`p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write `T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧`
for the extension of scalars `ℚ̄_ℓ,X ⊗ᴸ_{E_X} -` on bounded constructible complexes
(`ProEtale.constructibleToPadicAlgCl`). This file treats the clause on `f^!` of blueprint
`sk-prop-scalar-six` for the coefficient change `E ⟶ ℚ̄_ℓ`.

* **(Pull)** on bounded constructible complexes:
  `Lf^*_E ⋙ T_X ≅ T_Y ⋙ Lf^*_{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleUpperStarToPadicAlgClIso`), the restriction of
  `ProEtale.CondensedRing.derivedPullIso`.
* **(Push)** for a proper `g`: `Rg_*^E ⋙ T_Y ≅ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarToPadicAlgClIso`), the restriction of
  `ProEtale.CondensedRing.derivedPushHom`, an isomorphism for proper `g`.
* **(Shriek)** for an open immersion `j`: `j_!^E ⋙ T_X ≅ T_U ⋙ j_!^{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso`), and for
  every `f`: `Rf_!^E ⋙ T_Y ≅ T_X ⋙ Rf_!^{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekToPadicAlgClIso`), composed from the
  two along the chosen compactification.
* **The exchange for `f^!`**: the mate `Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_{ℚ̄_ℓ}` of the inverse of
  (Shriek) under the adjunctions `Rf_! ⊣ Rf^!`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekToPadicAlgCl`). For an open immersion
  `j` the exchange `j^*_E ⋙ T_U ⟶ T_X ⋙ j^*_{ℚ̄_ℓ}` is an isomorphism
  (`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionUpperStarToPadicAlgCl`), `j_!`
  being fully faithful and `j^*` commuting with `T` by (Pull). The exchange for `f^!` is the
  horizontal composite of the exchanges for the open and the proper part of the compactification
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl_eq`), so
  it is an isomorphism as soon as the exchange `Rg^!_E ⋙ T_Z ⟶ T_Y ⋙ Rg^!_{ℚ̄_ℓ}` for the proper
  part `g` is one
  (`ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekToPadicAlgCl_of_isIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The extension of scalars `T_X` on bounded constructible complexes is compatible with the
inclusions. -/
noncomputable def constructibleToPadicAlgClCompatibility :
    constructibleToPadicAlgCl X ℓ E ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ derivedExtendScalarsToPadicAlgCl X ℓ E :=
  ObjectProperty.liftCompιIso _ _ _

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### (Pull) -/

section UpperStar

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- **(Pull)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ`:
`Lf^*_E ⋙ T_X ≅ T_Y ⋙ Lf^*_{ℚ̄_ℓ}`, the restriction of `ProEtale.CondensedRing.derivedPullIso`
along the fully faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarToPadicAlgClIso :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ f ⋙
        constructibleToPadicAlgCl X.left ℓ E ≅
      constructibleToPadicAlgCl Y.left ℓ E ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (constructibleToPadicAlgClCompatibility X.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleUpperStarCompatibility _ ℓ f) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (constructibleToPadicAlgClCompatibility Y.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarCompatibility _ ℓ f).symm ≪≫
      (Functor.associator _ _ _).symm)

end UpperStar

/-! ### (Push) for a proper morphism -/

section LowerStar

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]

/-- **(Push)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ` and a proper
morphism `g`: `Rg_*^E ⋙ T_Y ≅ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`, the restriction of
`ProEtale.CondensedRing.derivedPushHom`, which is an isomorphism for proper `g`
(`ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`). -/
noncomputable def boundedConstructibleLowerStarToPadicAlgClIso :
    boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ g ⋙
        constructibleToPadicAlgCl Y.left ℓ E ≅
      constructibleToPadicAlgCl Z.left ℓ E ⋙
        boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ g :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (constructibleToPadicAlgClCompatibility Y.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleLowerStarCompatibility _ ℓ g) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (asIso (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) g.left)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (constructibleToPadicAlgClCompatibility Z.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarCompatibility _ ℓ g).symm ≪≫
      (Functor.associator _ _ _).symm)

end LowerStar

/-! ### (Shriek) for an open immersion -/

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- **(Shriek)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ` and an open
immersion `j`: `j_!^E ⋙ T_X ≅ T_U ⋙ j_!^{ℚ̄_ℓ}`, the restriction of
`ProEtale.CondensedRing.derivedOpenImmersionShriekIso`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ j ⋙
        constructibleToPadicAlgCl X.left ℓ E ≅
      constructibleToPadicAlgCl U.left ℓ E ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (constructibleToPadicAlgClCompatibility X.left ℓ E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (derivedOpenImmersionShriekIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) j.left) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (constructibleToPadicAlgClCompatibility U.left ℓ E).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleOpenImmersionLowerShriekCompatibility _ ℓ j).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The exchange `j^*_E ⋙ T_U ⟶ T_X ⋙ j^*_{ℚ̄_ℓ}` for an open immersion `j`: the mate of the
inverse of (Shriek) under the adjunctions `j_! ⊣ j^*`. -/
noncomputable def boundedConstructibleOpenImmersionUpperStarToPadicAlgCl :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ j ⋙
        constructibleToPadicAlgCl U.left ℓ E ⟶
      constructibleToPadicAlgCl X.left ℓ E ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  mateEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E j).inv

/-- The exchange for an open immersion `j` is an isomorphism: `j_!` is fully faithful on both
sides, and `j^*` commutes with the extension of scalars by (Pull)
(`boundedConstructibleUpperStarToPadicAlgClIso`). -/
instance isIso_boundedConstructibleOpenImmersionUpperStarToPadicAlgCl :
    IsIso (boundedConstructibleOpenImmersionUpperStarToPadicAlgCl ℓ E j) :=
  isIso_mateEquiv_of_isIso_unit _ _ _ (boundedConstructibleUpperStarToPadicAlgClIso ℓ E j).symm

end OpenImmersion

/-! ### (Shriek) and the exchange for `f^!` -/

section Shriek

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- **(Shriek)** on bounded constructible complexes along a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, for the inclusion `E ⟶ ℚ̄_ℓ`:
`Rf_!(c)^E ⋙ T_Y ≅ T_X ⋙ Rf_!(c)^{ℚ̄_ℓ}`, composed of (Shriek) for the open immersion `i` and
(Push) for the proper `g`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso :
    boundedConstructibleLowerShriekOfCompactification (Profinite.continuousMapRingObj E) ℓ c ⋙
        constructibleToPadicAlgCl Y.left ℓ E ≅
      constructibleToPadicAlgCl X.left ℓ E ⋙
        boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarToPadicAlgClIso ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E c.overI) _ ≪≫
    Functor.associator _ _ _

/-- The exchange `Rg^!_E ⋙ T_Z ⟶ T_Y ⋙ Rg^!_{ℚ̄_ℓ}` for the proper part `g` of a compactification:
the mate of the inverse of (Push) under the adjunctions `Rg_* ⊣ Rg^!`. -/
noncomputable def boundedConstructibleProperUpperShriekToPadicAlgCl :
    (boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ c.overG).rightAdjoint ⋙
        constructibleToPadicAlgCl c.overObj.left ℓ E ⟶
      constructibleToPadicAlgCl Y.left ℓ E ⋙
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ c.overG).rightAdjoint :=
  mateEquiv (Adjunction.ofIsLeftAdjoint _) (Adjunction.ofIsLeftAdjoint _)
    (boundedConstructibleLowerStarToPadicAlgClIso ℓ E c.overG).inv

/-- The exchange `Rf^!(c)_E ⋙ T_X ⟶ T_Y ⋙ Rf^!(c)_{ℚ̄_ℓ}` along a compactification `c`: the mate
of the inverse of (Shriek) under the adjunctions `Rf_!(c) ⊣ Rf^!(c)`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl :
    boundedConstructibleUpperShriekOfCompactification (Profinite.continuousMapRingObj E) ℓ c ⋙
        constructibleToPadicAlgCl X.left ℓ E ⟶
      constructibleToPadicAlgCl Y.left ℓ E ⋙
        boundedConstructibleUpperShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ c :=
  mateEquiv (boundedConstructibleUpperShriekOfCompactificationAdjunction _ ℓ c)
    (boundedConstructibleUpperShriekOfCompactificationAdjunction _ ℓ c)
    (boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso ℓ E c).inv

set_option maxHeartbeats 400000 in
-- `mateEquiv_hcomp` is matched against the unfolded adjunction `Rf_!(c) ⊣ Rf^!(c)`.
/-- The exchange for `f^!` along a compactification `c = (X ⟶[i] Z ⟶[g] Y)` is the horizontal
composite of the exchange for the proper part `g` and of the exchange for the open immersion `i`:
the mates of a vertical composite of squares are the horizontal composite of the mates
(`CategoryTheory.mateEquiv_hcomp`). -/
lemma boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl_eq :
    boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl ℓ E c =
      TwoSquare.hComp (boundedConstructibleProperUpperShriekToPadicAlgCl ℓ E c)
        (boundedConstructibleOpenImmersionUpperStarToPadicAlgCl ℓ E c.overI) := by
  have h : (boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso ℓ E c).inv =
      TwoSquare.vComp (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E c.overI).inv
        (boundedConstructibleLowerStarToPadicAlgClIso ℓ E c.overG).inv := by
    ext K
    simp [boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso, TwoSquare.vComp]
  unfold boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl
  rw [h]
  exact mateEquiv_hcomp
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ c.overI)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ c.overI)
    (Adjunction.ofIsLeftAdjoint
      (boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ c.overG))
    (Adjunction.ofIsLeftAdjoint
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ c.overG))
    (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E c.overI).inv
    (boundedConstructibleLowerStarToPadicAlgClIso ℓ E c.overG).inv

/-- The exchange for `f^!` along a compactification `c` is an isomorphism as soon as the exchange
for its proper part is one, the exchange for the open immersion being an isomorphism. -/
lemma isIso_boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl
    [IsIso (boundedConstructibleProperUpperShriekToPadicAlgCl ℓ E c)] :
    IsIso (boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl ℓ E c) := by
  rw [boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl_eq]
  unfold TwoSquare.hComp
  infer_instance

end OfCompactification

variable (f : X ⟶ Y)

/-- **(Shriek)** on bounded constructible complexes, for the inclusion `E ⟶ ℚ̄_ℓ`:
`Rf_!^E ⋙ T_Y ≅ T_X ⋙ Rf_!^{ℚ̄_ℓ}`, along the chosen compactification. -/
noncomputable def boundedConstructibleLowerShriekToPadicAlgClIso :
    boundedConstructibleLowerShriek (Profinite.continuousMapRingObj E) ℓ f ⋙
        constructibleToPadicAlgCl Y.left ℓ E ≅
      constructibleToPadicAlgCl X.left ℓ E ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso ℓ E (compactificationOverField f)

/-- **The exchange for `f^!`**, for the inclusion `E ⟶ ℚ̄_ℓ`: the canonical natural transformation
`Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_{ℚ̄_ℓ}`, the mate of the inverse of (Shriek)
(`boundedConstructibleLowerShriekToPadicAlgClIso`) under the adjunctions `Rf_! ⊣ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekToPadicAlgCl :
    boundedConstructibleUpperShriek (Profinite.continuousMapRingObj E) ℓ f ⋙
        constructibleToPadicAlgCl X.left ℓ E ⟶
      constructibleToPadicAlgCl Y.left ℓ E ⋙
        boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleUpperShriekAdjunction _ ℓ f)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).inv

/-- The exchange for `f^!` is an isomorphism as soon as the exchange for the proper part of the
chosen compactification is one. -/
lemma isIso_boundedConstructibleUpperShriekToPadicAlgCl_of_isIso
    [IsIso (boundedConstructibleProperUpperShriekToPadicAlgCl ℓ E (compactificationOverField f))] :
    IsIso (boundedConstructibleUpperShriekToPadicAlgCl ℓ E f) :=
  isIso_boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl ℓ E _

end Shriek

end AlgebraicGeometry.ProEtale.CondensedRing
