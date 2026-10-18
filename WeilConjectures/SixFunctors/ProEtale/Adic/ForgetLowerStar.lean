/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension

/-!
# The derived pushforward of `ℓ`-adic sheaves on underlying sheaves

The derived pushforward `Rg_*` of `ℓ`-adic sheaves (sheaves of `ℚ̄_ℓ,X`-modules,
`AlgebraicGeometry.ProEtale.AdicSheaf`) commutes with taking underlying complexes:

- `AlgebraicGeometry.ProEtale.rightDerivedAdicLowerStarCompForgetIso`: with the underlying
  complexes of sheaves of `ℚ̄_ℓ`-modules. The forgetful functor from `ℚ̄_ℓ,X`-modules has the
  exact left adjoint `ℚ̄_ℓ,X ⊗ -`, every sheaf of `ℚ̄_ℓ`-modules being flat
  (`AlgebraicGeometry.ProEtale.flat_weilCoefficientsSheaf`), so it preserves K-injective
  complexes.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarCompWeilCoefficientsSheafToAbIso`: with the
  underlying complexes of abelian sheaves. Restriction of scalars along the flat ring map
  `ℤ → ℚ̄_ℓ` has the exact left adjoint `ℚ̄_ℓ ⊗ -`, and sheaves of `ULift ℤ`-modules are
  abelian sheaves.
- `AlgebraicGeometry.ProEtale.rightDerivedAdicLowerStarCompForgetAbIso`: the composite.

This is the coefficient bridge between the `ℓ`-adic sheaves of the finiteness theorem
(`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`) and the abelian sheaves `𝒪_{E,X}`,
`E_X`, `ℚ̄_ℓ,X` of `WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafLowerStar`.
-/

@[expose] public section
universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

example {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (g)_*ᵃ[l] ⋙ AdicSheaf.forget Y = AdicSheaf.forget Z ⋙ (g)_*[WeilCoefficients.{u} l] := rfl

/-- Every sheaf of `ℚ̄_ℓ`-modules on `X_proét` is flat, `ℚ̄_ℓ` being a field. -/
lemma flat_weilCoefficientsSheaf (X : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) : ObjectProperty.flat F :=
  ObjectProperty.prop_of_iso _ (asIso ((sheafificationAdjunction _ _).counit.app F))
    (GrothendieckTopology.flat_presheafToSheaf_obj (WeilCoefficients.{u} l)
      (Scheme.ProEt.topology X) F.obj fun _ ↦ (ModuleCat.flat_iff_flat _).2 inferInstance)

instance (X : Scheme.{u}) : PreservesFiniteLimits (Mod.free (adicConstantSheaf l X)) := by
  have : PreservesFiniteLimits (Mod.free (adicConstantSheaf l X) ⋙ AdicSheaf.forget X) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).1
      (flat_weilCoefficientsSheaf X (adicConstantSheaf l X))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (AdicSheaf.forget X)

instance (X : Scheme.{u}) : (AdicSheaf.forget (l := l) X).PreservesKInjectiveComplexes := by
  have : (Mod.free (adicConstantSheaf l X)).Additive :=
    (Mod.freeForgetAdjunction _).left_adjoint_additive
  have := (Mod.freeForgetAdjunction (adicConstantSheaf l X)).leftAdjoint_preservesColimits
  have : (Mod.free (adicConstantSheaf l X)).PreservesHomology := {}
  exact (Mod.freeForgetAdjunction _).preservesKInjectiveComplexes

/-- The pushforward of `ℓ`-adic sheaves lies over the pushforward of sheaves of
`ℚ̄_ℓ`-modules. -/
noncomputable def adicLowerStarCompForgetIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (g)_*ᵃ[l] ⋙ AdicSheaf.forget Y ≅ AdicSheaf.forget Z ⋙ (g)_*[WeilCoefficients.{u} l] :=
  Iso.refl _

/-- The forgetful functor from `ℓ`-adic sheaves to sheaves of `ℚ̄_ℓ`-modules commutes with the
derived pushforward. -/
noncomputable def rightDerivedAdicLowerStarCompForgetIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (g)_*ᵃ[l].rightDerivedFunctor ⋙ (AdicSheaf.forget Y).mapDerivedCategory ≅
      (AdicSheaf.forget Z).mapDerivedCategory ⋙
        ((g)_*[WeilCoefficients.{u} l]).rightDerivedFunctor :=
  Functor.isoWhiskerLeft _ (AdicSheaf.forget Y).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    Functor.rightDerivedFunctorCompIso' _ _ (adicLowerStarCompForgetIso g) ≪≫
    (Functor.rightDerivedFunctorCompIso' _ _ (Iso.refl _)).symm ≪≫
    Functor.isoWhiskerRight (AdicSheaf.forget Z).rightDerivedFunctorIsoMapDerivedCategory _

section Ab

variable (l) in
/-- The ring homomorphism `ℤ → ℚ̄_ℓ`, lifted to the universe `u + 1`. -/
noncomputable def uliftIntToWeilCoefficients :
    ULift.{u + 1} ℤ →+* ULift.{u + 1} (PadicAlgCl l) :=
  ULift.ringEquiv.symm.toRingHom.comp ((algebraMap ℤ (PadicAlgCl l)).comp
    ULift.ringEquiv.toRingHom)

variable (l) in
/-- `ℚ̄_ℓ` is flat over `ℤ`, being torsion-free. -/
lemma flat_uliftIntToWeilCoefficients : (uliftIntToWeilCoefficients.{u} l).Flat :=
  RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective ULift.ringEquiv.bijective)
    (RingHom.flat_algebraMap_iff.2 inferInstance))
    (RingHom.Flat.of_bijective ULift.ringEquiv.symm.bijective)

variable (l) in
/-- The underlying abelian sheaf of a sheaf of `ℚ̄_ℓ`-modules on `X_proét`. -/
noncomputable abbrev weilCoefficientsSheafToAb (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  sheafCompose _ (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})

instance (X : Scheme.{u}) : (weilCoefficientsSheafToAb l X).PreservesKInjectiveComplexes := by
  let Ψ := sheafCompose (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalars.{u + 1} (uliftIntToWeilCoefficients.{u} l))
  let Θ := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  have : Θ.IsEquivalence := isEquivalence_sheafCompose_of_isEquivalence _ _
  have : Ψ.PreservesKInjectiveComplexes := by
    have := preservesFiniteLimits_sheafExtendScalars X (flat_uliftIntToWeilCoefficients l)
    have : (sheafExtendScalars (uliftIntToWeilCoefficients.{u} l) X).Additive :=
      (sheafExtendScalarsAdjunction _ X).left_adjoint_additive
    have : (sheafExtendScalars (uliftIntToWeilCoefficients.{u} l) X).PreservesHomology :=
      Functor.preservesHomology_of_preservesMonos_and_cokernels _
    exact (sheafExtendScalarsAdjunction _ X).preservesKInjectiveComplexes
  have : Θ.Additive := { }
  have : Ψ.Additive := { }
  exact Functor.preservesKInjectiveComplexes_of_iso (F := Ψ ⋙ Θ) (Iso.refl _)


instance (X : Scheme.{u}) : PreservesFiniteLimits (weilCoefficientsSheafToAb l X) :=
  preservesFiniteLimits_of_natIso (F := sheafCompose (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalars.{u + 1} (uliftIntToWeilCoefficients.{u} l)) ⋙
      sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})) (Iso.refl _)

instance (X : Scheme.{u}) : PreservesFiniteColimits (weilCoefficientsSheafToAb l X) :=
  have : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).IsEquivalence :=
    isEquivalence_sheafCompose_of_isEquivalence _ _
  preservesFiniteColimits_of_natIso (F := sheafCompose (Scheme.ProEt.topology X)
    (ModuleCat.restrictScalars.{u + 1} (uliftIntToWeilCoefficients.{u} l)) ⋙
      sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})) (Iso.refl _)

instance {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    ((g)_*[WeilCoefficients.{u} l]).PreservesKInjectiveComplexes :=
  (ProEtale.upperStarLowerStarAdjunction _ g).preservesKInjectiveComplexes
/-- Taking underlying abelian sheaves commutes with the derived pushforward of sheaves of
`ℚ̄_ℓ`-modules. -/
noncomputable def rightDerivedLowerStarCompWeilCoefficientsSheafToAbIso {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) :
    ((g)_*[WeilCoefficients.{u} l]).rightDerivedFunctor ⋙
        (weilCoefficientsSheafToAb l Y).mapDerivedCategory ≅
      (weilCoefficientsSheafToAb l Z).mapDerivedCategory ⋙
        ((g)_*[Ab.{u + 1}]).rightDerivedFunctor :=
  Functor.isoWhiskerLeft _
      (weilCoefficientsSheafToAb l Y).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    Functor.rightDerivedFunctorCompIso' _ _
      (show (g)_*[WeilCoefficients.{u} l] ⋙ weilCoefficientsSheafToAb l Y ≅
        weilCoefficientsSheafToAb l Z ⋙ (g)_*[Ab.{u + 1}] from Iso.refl _) ≪≫
    (Functor.rightDerivedFunctorCompIso' _ _ (Iso.refl _)).symm ≪≫
    Functor.isoWhiskerRight
      (weilCoefficientsSheafToAb l Z).rightDerivedFunctorIsoMapDerivedCategory _

/-- **The coefficient bridge**: the derived pushforward of `ℓ`-adic sheaves, followed by taking
underlying complexes of abelian sheaves, is the derived pushforward of abelian sheaves of the
underlying complex. -/
noncomputable def rightDerivedAdicLowerStarCompForgetAbIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (g)_*ᵃ[l].rightDerivedFunctor ⋙ (AdicSheaf.forget Y).mapDerivedCategory ⋙
        (weilCoefficientsSheafToAb l Y).mapDerivedCategory ≅
      (AdicSheaf.forget Z).mapDerivedCategory ⋙
        (weilCoefficientsSheafToAb l Z).mapDerivedCategory ⋙
          ((g)_*[Ab.{u + 1}]).rightDerivedFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedAdicLowerStarCompForgetIso g) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompWeilCoefficientsSheafToAbIso g)

end Ab

end AlgebraicGeometry.ProEtale
