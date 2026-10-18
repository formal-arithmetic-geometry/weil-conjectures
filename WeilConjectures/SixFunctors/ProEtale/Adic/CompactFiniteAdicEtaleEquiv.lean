/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ExtensionByZeroAdicCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicEtaleEquiv
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-!
# The comparison of `Hom(Λ_Y, Ra_! Λ_X[n])` with `Hⁿ(Z_proét, i_! ℤ_ℓ/ℓᵐ)`

Let `a : X ⟶ Y` be a quasi-compact morphism with a compactification
`c = (X ⟶[i] Z ⟶[g] Y)`, `Z` quasi-compact and quasi-separated, and `Λ = ℤ/ℓᵐ`. The chain of
comparisons
`Hom_{D(Y_ét, Λ)}(Λ_Y, (Ra_! Λ_X)[n]) ≅ Hom_{D(Z_ét, Λ)}(Λ_Z, (i_! Λ_X)[n])
≅ Extⁿ_Λ(Λ_Z, i_! Λ_X) ≅ Hⁿ(Z_ét, i_! Λ_X) ≅ Hⁿ(Z_proét, ν^* i_! Λ_X)
≅ Hⁿ(Z_proét, i_! C(-, ℤ_ℓ/ℓᵐ))`
is given by an explicit additive equivalence
(`AlgebraicGeometry.ProEtale.compactUnitShiftAddEquivFiniteAdicH`), the compactly supported
analogue of `AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH`. It feeds the compactly
supported case of blueprint `thm-pod-degreewise-perfectness-over-a-field`.

The ingredients are:
* the adjunction `Lg^* ⊣ Rg_*` and `Lg^* Λ_Y ≅ Λ_Z`
  (`AlgebraicGeometry.Etale.unitShiftAddEquivRightDerivedLowerStar`);
* the exactness of the extension by zero `i_!`, so that its derived functor is computed in
  degree zero (`AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekUnitIso`);
* the comparison of `Ext` over `Λ` with abelian cohomology, and of étale with pro-étale
  cohomology;
* the commutation of the extension by zero with forgetting the `Λ`-module structure
  (`AlgebraicGeometry.Etale.sheafForget₂OpenImmersionLowerShriekIso`) and with `ν^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The extension by zero along an open immersion commutes with forgetting the `Λ`-module
structure: `forget (j_! F) ≅ j_! (forget F)`. Both are a left Kan extension followed by
sheafification, and the forgetful functor preserves colimits and sheafification. -/
noncomputable def sheafForget₂OpenImmersionLowerShriekIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sheafForget₂ Λ X).obj ((j)_!open[ModuleCat.{u + 1} Λ].obj F) ≅
      (j)_!open[AddCommGrpCat.{u + 1}].obj ((sheafForget₂ Λ U).obj F) :=
  let E := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let L := (MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j)).op
  have : PreservesColimitsOfSize.{u + 1, u + 1} E := ModuleCat.forget₂PreservesColimitsOfSize Λ
  have : X.smallEtaleTopology.PreservesSheafification E :=
    GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology E
  ((sheafComposeNatIso X.smallEtaleTopology E
    (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
      (L.lan.obj F.obj)).symm ≪≫
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
      ((E.lanCompIsoOfPreserves L).app F.obj)

variable {Λ}

/-- `Hom(Λ_Z, M[n]) ≅ Hom(Λ_Y, (Rg_* M)[n])`, through the adjunction `Lg^* ⊣ Rg_*` and
`Lg^* Λ_Y ≅ Λ_Z`, for any `M ∈ D(Z_ét, Λ)`. -/
noncomputable def unitShiftAddEquivRightDerivedLowerStar {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (M : DerivedCategoryModule Λ Z) (n : ℤ) :
    (𝟙_ (DerivedCategoryModule Λ Z) ⟶ M⟦n⟧) ≃+
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((g)_*[ModuleCat.{u + 1} Λ])).obj M)⟦n⟧) where
  toFun x := (derivedUpperStarLowerStarAdjunction _ g).homEquiv _ _
      ((leftDerivedUpperStarUnitIso _ g).hom ≫ x) ≫
    ((R((g)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app _
  invFun z := (leftDerivedUpperStarUnitIso _ g).inv ≫
    ((derivedUpperStarLowerStarAdjunction _ g).homEquiv _ _).symm
      (z ≫ ((R((g)_*[ModuleCat.{u + 1} Λ])).commShiftIso n).inv.app _)
  left_inv x := by simp
  right_inv z := by simp
  map_add' x x' := by
    simp [Adjunction.homEquiv_unit, Preadditive.comp_add, Preadditive.add_comp]

variable (Λ) in
/-- The derived extension by zero of `Λ_U` along an open immersion `j : U ⟶ X` is the abelian
extension by zero `j_! Λ_U` placed in degree `0`, `j_!` being exact. -/
noncomputable def mapDerivedCategoryOpenImmersionLowerShriekUnitIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (D((j)_!open[ModuleCat.{u + 1} Λ])).obj (𝟙_ (DerivedCategoryModule Λ U)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((j)_!open[ModuleCat.{u + 1} Λ].obj (Sheaf.constantRing U.smallEtaleTopology Λ)) :=
  (D((j)_!open[ModuleCat.{u + 1} Λ])).mapIso (unitIsoSingleFunctorConstantSheaf Λ U) ≪≫
    (((j)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _

variable (Λ) in
/-- The classes `Λ_Z ⟶ F[n]` of `D(Z_ét, Λ)`, for an étale sheaf `F` of `Λ`-modules placed in
degree `0`, are the classes of `Extⁿ(Λ_Z, F)`. -/
noncomputable def unitShiftSingleAddEquivExt (Z : Scheme.{u})
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    (𝟙_ (DerivedCategoryModule Λ Z) ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦(n : ℤ)⟧) ≃+
      Ext (Sheaf.constantRing Z.smallEtaleTopology Λ) F n :=
  (AddEquiv.mk' ((unitIsoSingleFunctorConstantSheaf Λ Z).homCongr (Iso.refl _)) fun f g ↦ by
      simp [Iso.homCongr_apply]).trans
    (Ext.homAddEquiv (C := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))).symm

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime] (m : ℕ)

/-- `ν^*` of the underlying abelian sheaf of the extension by zero `i_! Λ_U`, `Λ = ℤ/ℓᵐ`, is the
extension by zero `i_! C(-, ℤ_ℓ/ℓᵐ)` of pro-étale sheaves. -/
noncomputable def forgetComparisonUpperStarOpenImmersionLowerShriekConstantRingIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (forgetComparisonUpperStar l m X).obj
        ((j)_!open[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m)))].obj
          (Sheaf.constantRing U.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))) ≅
      (j)_!open[AddCommGrpCat.{u + 1}].obj
        (continuousSheaf U (ℤ_[l] ⧸ (PadicInt.powOpenAddSubgroup l m : AddSubgroup ℤ_[l]))) :=
  (comparisonUpperStar AddCommGrpCat.{u + 1} X).mapIso
      (Etale.sheafForget₂OpenImmersionLowerShriekIso _ j _) ≪≫
    (openImmersionLowerShriekComparisonUpperStarIso AddCommGrpCat.{u + 1} j).app _ ≪≫
      (ProEtale.openImmersionLowerShriek AddCommGrpCat.{u + 1} j).mapIso
        (forgetComparisonUpperStarConstantRingIso l m U)

/-- `Extⁿ_Λ(Λ_Z, F) ≅ Hⁿ(Z_proét, ν^* F)` for an étale sheaf `F` of `Λ`-modules, `Λ = ℤ/ℓᵐ`, on a
quasi-compact quasi-separated scheme `Z`. -/
noncomputable def extConstantRingAddEquivH (Z : Scheme.{u}) [CompactSpace Z]
    [QuasiSeparatedSpace Z]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m)))))
    (n : ℕ) :
    Ext (Sheaf.constantRing Z.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) F n ≃+
      Sheaf.H ((forgetComparisonUpperStar l m Z).obj F) n :=
  (AddEquiv.ofBijective _
    (Etale.bijective_mapExtComp_constantIntToRing (ULift.{u + 1} (ZMod (l ^ m))) Z F n)).trans
    (cohomologyComparisonAddEquiv Z _ n)

variable {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) [CompactSpace c.Z]
  [QuasiSeparatedSpace c.Z]

/-- **Compactly supported finite-level cohomology as étale classes, for a given
compactification.** For a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `a` with `Z`
quasi-compact and quasi-separated, `Hom_{D(Y_ét, Λ)}(Λ_Y, (Rf_!(c) Λ_X)[n]) ≅
Hⁿ(Z_proét, i_! C(-, ℤ_ℓ/ℓᵐ))`, `Λ = ℤ/ℓᵐ`. -/
noncomputable def compactUnitShiftAddEquivFiniteAdicHOfCompactification (n : ℕ) :
    (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) Y) ⟶
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m)))) c).obj (𝟙_ _))⟦(n : ℤ)⟧) ≃+
      CompactFiniteAdicH c.i l m n :=
  (Etale.unitShiftAddEquivRightDerivedLowerStar c.g _ (n : ℤ)).symm.trans <|
    (AddEquiv.mk' (((Iso.refl _).homCongr ((shiftFunctor _ (n : ℤ)).mapIso
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekUnitIso _ c.i)))) fun f g ↦ by
        simp [Iso.homCongr_apply]).trans <|
      (Etale.unitShiftSingleAddEquivExt _ c.Z _ n).trans <|
        (extConstantRingAddEquivH l m c.Z _ n).trans
          (Sheaf.H.mapAddEquiv
            (forgetComparisonUpperStarOpenImmersionLowerShriekConstantRingIso l m c.i) n)

variable [QuasiCompact a] [HasCompactification a]

/-- **Compactly supported finite-level cohomology as étale classes.** For a quasi-compact
`a : X ⟶ Y` with a compactification `c = (X ⟶[i] Z ⟶[g] Y)`, `Z` quasi-compact and
quasi-separated, `Hom_{D(Y_ét, Λ)}(Λ_Y, (Ra_! Λ_X)[n]) ≅ Hⁿ(Z_proét, i_! C(-, ℤ_ℓ/ℓᵐ))`,
`Λ = ℤ/ℓᵐ`. For `Y = Spec k` with `k` separably closed and `Z` proper over `k`, the right-hand
side is the compactly supported cohomology `Hⁿ_c(X, ℤ/ℓᵐ)`; this feeds the compactly supported
case of blueprint `thm-pod-degreewise-perfectness-over-a-field`. -/
noncomputable def compactUnitShiftAddEquivFiniteAdicH (n : ℕ) :
    (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) Y) ⟶
        ((R(a)_![ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ m)))]).obj (𝟙_ _))⟦(n : ℤ)⟧) ≃+
      CompactFiniteAdicH c.i l m n :=
  (AddEquiv.mk' ((Iso.refl _).homCongr ((shiftFunctor _ (n : ℤ)).mapIso
      ((Etale.rightDerivedLowerShriekIso _ c).app _).symm)) fun f g ↦ by
        simp [Iso.homCongr_apply]).trans
    (compactUnitShiftAddEquivFiniteAdicHOfCompactification l m c n)

end AlgebraicGeometry.ProEtale
