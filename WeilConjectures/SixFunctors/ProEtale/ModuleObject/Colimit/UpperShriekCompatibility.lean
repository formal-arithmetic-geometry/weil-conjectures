/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ToPadicAlgClCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityPush
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibility

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

The file is split for compile time: `T_X`, (Pull) and the open immersions are in
`…Colimit.UpperShriekCompatibilityPull`, (Push) in `…Colimit.UpperShriekCompatibilityPush`, the
exchange along a compactification in `…Colimit.UpperShriekCompatibilityCompactification`; this
module imports them and treats the exchange for `f^!` along the chosen compactification.

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
          (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).inv)).natTrans :=
  rfl

/-- The exchange for `f^!` is an isomorphism as soon as the exchange for the proper part of the
chosen compactification is one. -/
lemma isIso_boundedConstructibleUpperShriekToPadicAlgCl_of_isIso
    [IsIso (boundedConstructibleProperUpperShriekToPadicAlgCl ℓ E (compactificationOverField f))] :
    IsIso (boundedConstructibleUpperShriekToPadicAlgCl ℓ E f) :=
  isIso_boundedConstructibleUpperShriekOfCompactificationToPadicAlgCl ℓ E _

end Shriek

end AlgebraicGeometry.ProEtale.CondensedRing
