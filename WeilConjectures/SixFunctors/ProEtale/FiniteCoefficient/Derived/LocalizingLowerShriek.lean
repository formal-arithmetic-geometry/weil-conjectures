/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekTriangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarCoproducts
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekLocalizing

/-!
# Compact support along one compactification on `Loc(Dctf)`

Let `Λ` be a finite ring whose exponent is invertible on a finite-type `k`-scheme `Y`, and let
`c = (X ⟶[j] X̄ ⟶[p] Y)` be a compactification of `f : X ⟶ Y`. The compact-support functor
`Rf_!(c) = Rp_* ∘ j_!` of this one compactification (the construction underlying the independence
of `Rf_!` from the compactification)

* preserves coproducts of objects of `Loc(Dctf(X, Λ))`
  (`preservesColimitsOfShape_localizingClosure_rightDerivedLowerShriekOfCompactification`):
  `j_!` is a left adjoint and maps `Loc(Dctf(X, Λ))` into `Loc(Dctf(X̄, Λ))`
  (`AlgebraicGeometry.ProEtale.localizingClosure_constructibleFiniteTor_openImmersionLowerShriek`),
  and the proper direct image `Rp_*` preserves coproducts of objects of `Loc(Dctf(X̄, Λ))`
  (`preservesColimit_discrete_rightDerivedLowerStar_of_localizingClosure`, the direct-sum clause of
  *proper direct image on the localizing categories*; also in functor form
  `preservesColimitsOfShape_localizingClosure_rightDerivedLowerStar_of_isProper`), because such
  objects have cohomology sheaves of étale origin and
  `Rp_*` commutes with coproducts of such complexes
  (`AlgebraicGeometry.ProEtale.isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology`);
* hence maps `Loc(Dctf(X, Λ))` into `Loc(Dctf(Y, Λ))`
  (`AlgebraicGeometry.ProEtale.localizingClosure_rightDerivedLowerShriekOfCompactification_obj`),
  since it maps `Dctf(X, Λ)` into `Dctf(Y, Λ)`
  (`AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedLowerShriekOfCompactification`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  {f : X ⟶ Y} (c : Compactification f)

/-- *Proper direct image on the localizing categories*, the direct-sum clause: for a proper
morphism `p : Z ⟶ Y` of finite-type `k`-schemes, `Rp_*` preserves coproducts of objects of
`Loc(Dctf(Z, Λ))`. Such objects have cohomology sheaves of étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.localizingClosure_constructibleFiniteTor_le`), and
the proper direct image commutes with coproducts of such complexes
(`AlgebraicGeometry.ProEtale.isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology`).
-/
theorem preservesColimit_discrete_rightDerivedLowerStar_of_localizingClosure {Z : Scheme.{u}}
    (p : Z ⟶ Y) [IsProper p] (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (hp : p ≫ aY = aZ) {J : Type (u + 1)}
    (N : J → _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)))
    (hN : ∀ j, (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z).localizingClosure
      (N j)) :
    PreservesColimit (Discrete.functor N)
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
  have := isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology Λ p aZ aY hp N
    fun j ↦ DerivedCategory.localizingClosure_constructibleFiniteTor_le Λ Z _ (hN j)
  PreservesCoproduct.of_iso_comparison _ _

/-- *Proper direct image on the localizing categories*, the direct-sum clause in functor form:
for a proper morphism `p : Z ⟶ Y` of finite-type `k`-schemes, the restriction of `Rp_*` to
`Loc(Dctf(Z, Λ))` preserves coproducts
(`AlgebraicGeometry.ProEtale.preservesColimit_discrete_rightDerivedLowerStar_of_localizingClosure`).
-/
theorem preservesColimitsOfShape_localizingClosure_rightDerivedLowerStar_of_isProper
    {Z : Scheme.{u}} (p : Z ⟶ Y) [IsProper p] (aZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType aZ]
    [QuasiCompact aZ] (hp : p ≫ aY = aZ) (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z).localizingClosure.ι ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor) := by
  let L := (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z).localizingClosure
  have (M : J → L.FullSubcategory) : PreservesColimit (Discrete.functor M)
      (L.ι ⋙ (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor) := by
    have := preservesColimit_discrete_rightDerivedLowerStar_of_localizingClosure Λ aY p aZ hp
      (fun j ↦ (M j).obj) fun j ↦ (M j).property
    have : PreservesColimit (Discrete.functor ((Discrete.functor M ⋙ L.ι).obj ∘ Discrete.mk))
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor := this
    have : PreservesColimit (Discrete.functor M ⋙ L.ι)
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
      preservesColimit_of_iso_diagram _
        (Discrete.natIsoFunctor (F := Discrete.functor M ⋙ L.ι)).symm
    exact inferInstanceAs (PreservesColimit (Discrete.functor M)
      (L.ι ⋙ (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor))
  exact preservesColimitsOfShape_of_discrete _

include aY in
/-- The compact-support functor `Rf_!(c) = Rp_* ∘ j_!` of one compactification `c` preserves
coproducts of objects of `Loc(Dctf(X, Λ))`: `j_!` maps
`Loc(Dctf(X, Λ))` into `Loc(Dctf(X̄, Λ))` and preserves coproducts
(`AlgebraicGeometry.ProEtale.localizingClosure_constructibleFiniteTor_openImmersionLowerShriek`),
and `Rp_*` preserves coproducts of objects of `Loc(Dctf(X̄, Λ))`
(`AlgebraicGeometry.ProEtale.preservesColimit_discrete_rightDerivedLowerStar_of_localizingClosure`).
-/
theorem preservesColimitsOfShape_localizingClosure_rightDerivedLowerShriekOfCompactification
    (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure.ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ aY)
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace (c.g ≫ aY)
  have : IsNoetherian c.Z := {}
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  let L := (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure
  let Φ := L.ι ⋙ (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategory
  have (M : J → L.FullSubcategory) : PreservesColimit (Discrete.functor M)
      (L.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) := by
    -- `j_!` maps `Loc(Dctf(X, Λ))` into `Loc(Dctf(X̄, Λ))`
    have hM (j : J) :
        (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) c.Z).localizingClosure
          (Φ.obj (M j)) :=
      (localizingClosure_constructibleFiniteTor_openImmersionLowerShriek.{u + 1, u} Λ c.i).2.2 _
        (M j).property
    -- `Rp_*` preserves coproducts of objects of `Loc(Dctf(X̄, Λ))`
    have : PreservesColimit (Discrete.functor fun j ↦ Φ.obj (M j))
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctor :=
      preservesColimit_discrete_rightDerivedLowerStar_of_localizingClosure Λ aY c.g (c.g ≫ aY)
        rfl _ hM
    have : PreservesColimit (Discrete.functor ((Discrete.functor M ⋙ Φ).obj ∘ Discrete.mk))
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctor := this
    have : PreservesColimit (Discrete.functor M ⋙ Φ)
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctor :=
      preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := Discrete.functor M ⋙ Φ)).symm
    exact inferInstanceAs (PreservesColimit (Discrete.functor M)
      (Φ ⋙ (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctor))
  exact preservesColimitsOfShape_of_discrete _

include aY in
/-- The compact-support functor `Rf_!(c)` of one compactification `c` maps `Loc(Dctf(X, Λ))` into
`Loc(Dctf(Y, Λ))`. -/
theorem localizingClosure_rightDerivedLowerShriekOfCompactification_obj [HasInvertibleExponent Λ Y]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure K) :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).localizingClosure
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K) :=
  have := preservesColimitsOfShape_localizingClosure_rightDerivedLowerShriekOfCompactification
    Λ aY c
  ObjectProperty.localizingClosure_obj_of_le _ _ _
    (fun _ hK ↦ ObjectProperty.le_localizingClosure _ _
      (constructibleFiniteTor_rightDerivedLowerShriekOfCompactification Λ aY c hK)) K hK

end AlgebraicGeometry.ProEtale
