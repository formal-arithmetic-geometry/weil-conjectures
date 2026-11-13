/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek

/-!

# Compatibility of `Rf^!` with the extension of scalars `E ⟶ ℚ̄_ℓ`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, and `k` a field of characteristic
`p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write `T_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧`
for the extension of scalars `ℚ̄_ℓ,X ⊗ᴸ_{E_X} -` on bounded constructible complexes
(`ProEtale.CondensedRing.boundedConstructibleToPadicAlgCl`, the functor
`ProEtale.constructibleToPadicAlgCl` typed on the categories `Dᵇc(X)⟦Λ⟧`). This file treats the
clause on `f^!` of blueprint `sk-prop-scalar-six` for the coefficient change `E ⟶ ℚ̄_ℓ`. The
comparisons (Pull), (Push) and (Shriek) for open immersions are in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility`.

* **(Pull)** on bounded constructible complexes:
  `Lf^*_E ⋙ T_X ≅ T_Y ⋙ Lf^*_{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleUpperStarToPadicAlgClIso`), the restriction of
  `ProEtale.CondensedRing.derivedPullIso`.
* **(Push)** for a proper `g`: `Rg_*^E ⋙ T_Y ≅ T_Z ⋙ Rg_*^{ℚ̄_ℓ}`
  (`ProEtale.CondensedRing.boundedConstructibleLowerStarToPadicAlgClIso`), the restriction of
  `ProEtale.CondensedRing.derivedPushHom`, an isomorphism at bounded below complexes.
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
  (`ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekToPadicAlgCl_of_isIso`). That it
  is one, and hence that the exchange for `f^!` is an isomorphism, is proved in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityProper`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

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
    ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙
        boundedConstructibleToPadicAlgCl Y.left ℓ E ≅
      boundedConstructibleToPadicAlgCl X.left ℓ E ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarToPadicAlgClIso ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekToPadicAlgClIso ℓ E c.overI) _ ≪≫
    Functor.associator _ _ _

/-- The exchange `Rg^!_E ⋙ T_Z ⟶ T_Y ⋙ Rg^!_{ℚ̄_ℓ}` for the proper part `g` of a compactification:
the mate of the inverse of (Push) under the adjunctions `Rg_* ⊣ Rg^!`. -/
noncomputable def boundedConstructibleProperUpperShriekToPadicAlgCl :
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E c.overG).rightAdjoint ⋙
        boundedConstructibleToPadicAlgCl c.overObj.left ℓ E ⟶
      boundedConstructibleToPadicAlgCl Y.left ℓ E ⋙
        (boundedConstructibleLowerStar ℓ c.overG).rightAdjoint :=
  mateEquiv (Adjunction.ofIsLeftAdjoint _) (Adjunction.ofIsLeftAdjoint _)
    (boundedConstructibleLowerStarToPadicAlgClIso ℓ E c.overG).inv

/-- The exchange `Rf^!(c)_E ⋙ T_X ⟶ T_Y ⋙ Rf^!(c)_{ℚ̄_ℓ}` along a compactification `c`: the mate
of the inverse of (Shriek) under the adjunctions `Rf_!(c) ⊣ Rf^!(c)`. -/
noncomputable def boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl :
    ContinuousMapRingObj.boundedConstructibleUpperShriekOfCompactification ℓ E c ⋙
        boundedConstructibleToPadicAlgCl X.left ℓ E ⟶
      boundedConstructibleToPadicAlgCl Y.left ℓ E ⋙
        boundedConstructibleUpperShriekOfCompactification ℓ c :=
  mateEquiv
    (ContinuousMapRingObj.boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ E c)
    (boundedConstructibleUpperShriekOfCompactificationAdjunction ℓ c)
    (boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso ℓ E c).inv

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
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.continuousMapRingObj E) ℓ c.overI)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)
    (Adjunction.ofIsLeftAdjoint
      (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E c.overG))
    (Adjunction.ofIsLeftAdjoint
      (boundedConstructibleLowerStar ℓ c.overG))
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
    ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
        boundedConstructibleToPadicAlgCl Y.left ℓ E ≅
      boundedConstructibleToPadicAlgCl X.left ℓ E ⋙
        boundedConstructibleLowerShriek ℓ f :=
  boundedConstructibleLowerShriekOfCompactificationToPadicAlgClIso ℓ E (compactificationOverField f)

/-- **The exchange for `f^!`**, for the inclusion `E ⟶ ℚ̄_ℓ`: the canonical natural transformation
`Rf^!_E ⋙ T_X ⟶ T_Y ⋙ Rf^!_{ℚ̄_ℓ}`, the mate of the inverse of (Shriek)
(`boundedConstructibleLowerShriekToPadicAlgClIso`) under the adjunctions `Rf_! ⊣ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekToPadicAlgCl :
    ContinuousMapRingObj.boundedConstructibleUpperShriek ℓ E f ⋙
        boundedConstructibleToPadicAlgCl X.left ℓ E ⟶
      boundedConstructibleToPadicAlgCl Y.left ℓ E ⋙
        boundedConstructibleUpperShriek ℓ f :=
  mateEquiv (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).inv

/-- The exchange for `f^!` as the mate of a two-square. -/
lemma boundedConstructibleUpperShriekToPadicAlgCl_eq_mateEquiv :
    boundedConstructibleUpperShriekToPadicAlgCl ℓ E f =
      (mateEquiv (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
        (boundedConstructibleUpperShriekAdjunction ℓ f)
        (TwoSquare.mk _ _ _ _
          (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).inv)) :=
  rfl

/-- The exchange for `f^!` is an isomorphism as soon as the exchange for the proper part of the
chosen compactification is one. -/
lemma isIso_boundedConstructibleUpperShriekToPadicAlgCl_of_isIso
    [IsIso (boundedConstructibleProperUpperShriekToPadicAlgCl ℓ E (compactificationOverField f))] :
    IsIso (boundedConstructibleUpperShriekToPadicAlgCl ℓ E f) :=
  isIso_boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl ℓ E _

end Shriek

end AlgebraicGeometry.ProEtale.CondensedRing
