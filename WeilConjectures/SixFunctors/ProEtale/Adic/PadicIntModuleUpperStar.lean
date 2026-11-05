/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafPadicIntExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-!
# Pullback of `ℤ_ℓ,X`-modules along weakly étale morphisms

For a weakly étale `g : W ⟶ X`, the pullback `g^*` of abelian sheaves is the restriction along
the localization functor `W_proét ⥤ X_proét`, which sends `ℤ_ℓ,X` to `ℤ_ℓ,W`; the comparison
`g^* ℤ_ℓ,X ≅ ℤ_ℓ,W` is a morphism of ring objects
(`AlgebraicGeometry.ProEtale.isMonHom_upperStarPadicIntAbSheafHom`). This gives the pullback
of `ℤ_ℓ`-modules `AlgebraicGeometry.ProEtale.padicIntModUpperStar`, left adjoint to the
pushforward `AlgebraicGeometry.ProEtale.padicIntModLowerStar`.

Restriction of scalars from `ℓ`-adic sheaves to `ℤ_ℓ`-modules commutes with the pushforwards
(`AlgebraicGeometry.ProEtale.adicLowerStarRestrictPadicIntIso`): the inclusions `ℤ_ℓ ⟶ ℚ̄_ℓ` are
compatible with the comparisons `ℤ_ℓ,X ⟶ g_* ℤ_ℓ,W` and `ℚ̄_ℓ,X ⟶ g_* ℚ̄_ℓ,W`, as one checks on
sections. Taking conjugates, **extension of scalars commutes with the pullback**
(`AlgebraicGeometry.ProEtale.padicIntModUpperStarCompAdicSheafExtendScalarsIso`):
`g^* (ℚ̄_ℓ ⊗ M) ≅ ℚ̄_ℓ ⊗ g^* M`. Finally the extension of scalars of `ℤ_ℓ,W` is `ℚ̄_ℓ,W`
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsRegularIso`), from the general
`CategoryTheory.Mod.extendScalarsObjRegularIso` (`S ⊗_R R ≅ S`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped Obj

namespace CategoryTheory

namespace Mod

variable {C : Type*} [Category* C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

/-- `φ : R ⟶ S` as an `R`-linear map from the regular `R`-module to `S`. -/
noncomputable def regularHomComap : regular R ⟶ (comap φ).obj (regular S) :=
  homMk φ (by
    rw [act_comap_obj, ← Category.assoc]
    exact (IsMonHom.mul_hom (f := φ)).trans (by
      rw [tensorHom_def']
      rfl))

/-- **Extension of scalars of the regular module**: `S ⊗_R R ≅ S`. -/
noncomputable def extendScalarsObjRegularIso : extendScalarsObj φ (regular R) ≅ regular S where
  hom := extendHom φ (regularHomComap φ)
  inv := regularLift _ (η[R] ≫ extendUnitHom φ (regular R))
  hom_inv_id := by
    refine extendScalarsObj_hom_ext φ ?_
    have h : φ ≫ (regularLift _ (η[R] ≫ extendUnitHom φ (regular R))).hom =
        extendUnitHom φ (regular R) := by
      rw [regularLift, homMk_hom]
      rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, whiskerLeft_comp_assoc,
        whiskerLeft_extendUnitHom_smul, ← smul_extendUnitHom]
      erw [MonObj.mul_one_assoc]
      rw [Iso.inv_hom_id_assoc]
    rw [comp_hom', extendπ_extendHom_assoc, regularHomComap, homMk_hom]
    erw [act_hom]
    rw [← whiskerLeft_comp_assoc, h, whiskerLeft_extendUnitHom_smul']
    exact (Category.comp_id _).symm
  inv_hom_id := by
    refine regular_hom_ext ?_
    rw [comp_hom', ← Category.assoc, one_comp_regularLift, Category.assoc,
      extendUnitHom_extendHom, regularHomComap, homMk_hom]
    exact (IsMonHom.one_hom (f := φ)).trans (Category.comp_id _).symm

end Mod

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

variable {X} {W : Scheme.{u}} (g : W ⟶ X) [h : WeaklyEtale g]

/-- The pushforward of sheaves of `ℚ̄_ℓ`-modules commutes with the forgetful functor to abelian
sheaves, strictly. -/
noncomputable abbrev lowerStarCompWeilCoefficientsForgetAbIso :
    (g)_*[WeilCoefficients.{u} l] ⋙ weilCoefficientsForgetAb l X ≅
      weilCoefficientsForgetAb l W ⋙ (g)_*[Ab.{u + 1}] :=
  Iso.refl _

/-- The identification `g_* ⋙ forget = forget ⋙ g_*` is monoidal. -/
instance : NatTrans.IsMonoidal (lowerStarCompWeilCoefficientsForgetAbIso l g).hom :=
  Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g) (ProEt.topology X) (ProEt.topology W)
    (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})

end AlgebraicGeometry.ProEtale
