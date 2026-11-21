/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MatesHCompIsIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.UpperShriekCompatibilityProper

/-!
# Compatibility of `Rf^!` with the composite extension of scalars `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and
`k` a field of characteristic `p ≠ ℓ`. For a separated `k`-scheme of finite type `X` write
`T_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧` and `T'_X : Dᵇc(X)⟦E⟧ ⥤ Dᵇc(X)⟦ℚ̄_ℓ⟧` for the extensions of
scalars. For a morphism `f : X ⟶ Y` of separated `k`-schemes of finite type:

* `ProEtale.CondensedRing.boundedConstructibleLowerShriekIntegersToPadicAlgClIso`: the comparison
  `Rf_!^{𝒪_E} ⋙ T_Y ⋙ T'_Y ≅ (T_X ⋙ T'_X) ⋙ Rf_!^{ℚ̄_ℓ}` for the composite extension of
  scalars, the composite of the comparisons along `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ`;
* `ProEtale.CondensedRing.boundedConstructibleUpperShriekIntegersToPadicAlgCl`: the exchange
  `Rf^!_{𝒪_E} ⋙ T_X ⋙ T'_X ⟶ (T_Y ⋙ T'_Y) ⋙ Rf^!_{ℚ̄_ℓ}`, its mate under `Rf_! ⊣ Rf^!`;
* `ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekIntegersToPadicAlgCl`: this exchange
  is an isomorphism.

## Implementation details

The mate of a horizontal composite of 2-squares is the vertical composite of the mates
(`CategoryTheory.mateEquiv_vcomp`), so the exchange for the composite is an isomorphism because the
exchanges along `𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ` are
(`CategoryTheory.isIso_mateEquiv_isoHComp`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The comparison `(T_X ⋙ T'_X) ⋙ Rf_!^{ℚ̄_ℓ} ≅ Rf_!^{𝒪_E} ⋙ (T_Y ⋙ T'_Y)` for the composite
extension of scalars `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`: the horizontal composite of the comparisons for
`𝒪_E ⟶ E` and `E ⟶ ℚ̄_ℓ`, along the chosen compactification. -/
noncomputable def boundedConstructibleLowerShriekIntegersToPadicAlgClIso :
    (boundedConstructibleExtendScalars X.left ℓ E ⋙ boundedConstructibleToPadicAlgCl X.left ℓ E) ⋙
        boundedConstructibleLowerShriek ℓ f ≅
      PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E.1 f ⋙
        (boundedConstructibleExtendScalars Y.left ℓ E ⋙
          boundedConstructibleToPadicAlgCl Y.left ℓ E) :=
  Functor.isoHComp (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).symm
    (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).symm

/-- The exchange for `f^!` along the composite extension of scalars `𝒪_E ⟶ E ⟶ ℚ̄_ℓ`: the
natural transformation `Rf^!_{𝒪_E} ⋙ (T_X ⋙ T'_X) ⟶ (T_Y ⋙ T'_Y) ⋙ Rf^!_{ℚ̄_ℓ}`, the mate of
`boundedConstructibleLowerShriekIntegersToPadicAlgClIso` under the adjunctions `Rf_! ⊣ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekIntegersToPadicAlgCl :
    PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E.1 f ⋙
        (boundedConstructibleExtendScalars X.left ℓ E ⋙
          boundedConstructibleToPadicAlgCl X.left ℓ E) ⟶
      (boundedConstructibleExtendScalars Y.left ℓ E ⋙
          boundedConstructibleToPadicAlgCl Y.left ℓ E) ⋙
        boundedConstructibleUpperShriek ℓ f :=
  mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleLowerShriekIntegersToPadicAlgClIso ℓ E f).hom

/-- The exchange for `f^!` along the composite extension of scalars `𝒪_E ⟶ E ⟶ ℚ̄_ℓ` is an
isomorphism on bounded constructible complexes. -/
theorem isIso_boundedConstructibleUpperShriekIntegersToPadicAlgCl :
    IsIso (boundedConstructibleUpperShriekIntegersToPadicAlgCl ℓ E f) := by
  have : IsIso (mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
      (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (boundedConstructibleLowerShriekExtendScalarsIso ℓ E f).symm.hom) :=
    isIso_boundedConstructibleUpperShriekExtendScalars ℓ E f
  have : IsIso (mateEquiv (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
      (boundedConstructibleUpperShriekAdjunction ℓ f)
      (boundedConstructibleLowerShriekToPadicAlgClIso ℓ E f).symm.hom) :=
    isIso_boundedConstructibleUpperShriekToPadicAlgCl ℓ E f
  exact isIso_mateEquiv_isoHComp
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E.1 f)
    (ContinuousMapRingObj.boundedConstructibleUpperShriekAdjunction ℓ E f)
    (boundedConstructibleUpperShriekAdjunction ℓ f) _ _

end AlgebraicGeometry.ProEtale.CondensedRing
