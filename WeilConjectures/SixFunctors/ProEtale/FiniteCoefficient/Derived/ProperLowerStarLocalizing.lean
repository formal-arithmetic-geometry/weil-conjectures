/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing

/-!
# The proper direct image on `Loc(Dctf)`, finite coefficients

Let `Λ` be a finite ring whose exponent is invertible on a finite-type `k`-scheme `Y`, and let
`p : X ⟶ Y` be proper. The pro-étale direct image `Rp_*` (a triangulated functor of the ambient
derived categories, hence exact)

* maps `Dctf(X, Λ)` into `Dctf(Y, Λ)`
  (`DerivedCategory.constructibleFiniteTor_rightDerivedLowerStar`):
  on `ν^* G` it is `ν^* Rp_*^{ét} G`, and the étale `Rp_*` preserves `Dctf`;
* preserves direct sums of objects of `Loc(Dctf(X, Λ))`
  (`DerivedCategory.preservesColimitsOfShape_localizing_rightDerivedLowerStar`, blueprint
  `proposition-proper-direct-image-extension-zero--2`), these having cohomology sheaves
  of étale origin;
* hence maps `Loc(Dctf(X, Λ))` into `Loc(Dctf(Y, Λ))`
  (`DerivedCategory.localizingConstructibleFiniteTor_rightDerivedLowerStar`, blueprint
  `proposition-proper-direct-image-extension-zero--1` for finite coefficients).

Together: blueprint `corollary-proper-direct-image-finite-coefficients-localizing--1`
(`localizingConstructibleFiniteTor_rightDerivedLowerStar_and_preservesColimitsOfShape`, in
the namespace `AlgebraicGeometry.ProEtale.DerivedCategory`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  (p : X ⟶ Y) [IsProper p]

include aY in
/-- The pro-étale direct image along a proper morphism `p : X ⟶ Y` to a finite-type `k`-scheme
maps `Dctf(X, Λ)` into `Dctf(Y, Λ)`, for a finite `Λ` whose exponent is invertible on `Y`. -/
theorem constructibleFiniteTor_rightDerivedLowerStar [HasInvertibleExponent Λ Y]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.obj K) := by
  obtain ⟨⟨G, hG, ⟨e⟩⟩, a, b, hab⟩ := hK
  have hGt : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X G :=
    ⟨hG, a, b, (torAmplitudeIn_mapDerivedCategory_iff a b G).1
      ((torAmplitudeIn _ X a b).prop_of_iso e.symm hab)⟩
  exact (constructibleFiniteTor _ Y).prop_of_iso
    ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.mapIso e.symm ≪≫
      (rightDerivedLowerStarComparisonIso _ p).app ⟨G, hG.1.1⟩).symm
    (constructibleFiniteTor_mapDerivedCategory Λ
      (Etale.constructibleFiniteTor_rightDerivedLowerStar Λ (p ≫ aY) aY p rfl hGt))

include aY in
/-- Blueprint `proposition-proper-direct-image-extension-zero--2`: Proper direct sums, finite
coefficients. For a proper `p : X ⟶ Y` to a finite-type `k`-scheme and a finite ring `Λ`, the
direct image `Rp_*` preserves direct sums of objects of `Loc(Dctf(X_proét, Λ))`. -/
theorem preservesColimitsOfShape_localizing_rightDerivedLowerStar (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      ((localizingConstructibleFiniteTor Λ X).ι ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor) := by
  let L := localizingConstructibleFiniteTor Λ X
  have (M : J → L.FullSubcategory) : PreservesColimit (Discrete.functor M)
      (L.ι ⋙ (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor) := by
    have := isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology Λ p
      (p ≫ aY) aY rfl (fun j ↦ L.ι.obj (M j))
      (fun j ↦ localizingClosure_constructibleFiniteTor_le Λ X _ (M j).property)
    have : PreservesColimit (Discrete.functor fun j ↦ L.ι.obj (M j))
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
      PreservesCoproduct.of_iso_comparison _ _
    have : PreservesColimit (Discrete.functor ((Discrete.functor M ⋙ L.ι).obj ∘ Discrete.mk))
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor := this
    have : PreservesColimit (Discrete.functor M ⋙ L.ι)
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
      preservesColimit_of_iso_diagram _
        (Discrete.natIsoFunctor (F := Discrete.functor M ⋙ L.ι)).symm
    infer_instance
  exact preservesColimitsOfShape_of_discrete _

include aY in
/-- Blueprint `proposition-proper-direct-image-extension-zero--1`, finite coefficients: for a
proper `p : X ⟶ Y` to a finite-type `k`-scheme and a finite ring `Λ` whose exponent is
invertible on `Y`, the direct image `Rp_*` (exact, being a triangulated functor of the ambient
derived categories) restricts to a functor `Loc(Dctf(X, Λ)) ⥤ Loc(Dctf(Y, Λ))`: it maps
`Loc(Dctf(X, Λ))` into `Loc(Dctf(Y, Λ))`. -/
theorem localizingConstructibleFiniteTor_rightDerivedLowerStar [HasInvertibleExponent Λ Y]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : localizingConstructibleFiniteTor Λ X K) :
    localizingConstructibleFiniteTor Λ Y
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.obj K) :=
  have := preservesColimitsOfShape_localizing_rightDerivedLowerStar Λ aY p
  ObjectProperty.localizingClosure_obj_of_le _ _ _
    (fun _ hK ↦ ObjectProperty.le_localizingClosure _ _
      (constructibleFiniteTor_rightDerivedLowerStar Λ aY p hK)) K hK

include aY in
/-- Blueprint `corollary-proper-direct-image-finite-coefficients-localizing--1`: Proper direct
image on the localizing categories. Let `Λ` be a finite ring whose exponent is invertible on the
finite-type `k`-scheme `Y`, and let `p : X ⟶ Y` be proper. The direct image `Rp_*`, a
triangulated (hence exact) functor of the ambient derived categories, restricts to a functor
`Loc(Dctf(X, Λ)) ⥤ Loc(Dctf(Y, Λ))`, and this restriction preserves arbitrary direct sums. -/
theorem localizingConstructibleFiniteTor_rightDerivedLowerStar_and_preservesColimitsOfShape
    [HasInvertibleExponent Λ Y] :
    (∀ K, localizingConstructibleFiniteTor Λ X K →
      localizingConstructibleFiniteTor Λ Y
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor.obj K)) ∧
    ∀ J : Type (u + 1), PreservesColimitsOfShape (Discrete J)
      ((localizingConstructibleFiniteTor Λ X).ι ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor) :=
  ⟨localizingConstructibleFiniteTor_rightDerivedLowerStar Λ aY p,
    preservesColimitsOfShape_localizing_rightDerivedLowerStar Λ aY p⟩

end AlgebraicGeometry.ProEtale.DerivedCategory
