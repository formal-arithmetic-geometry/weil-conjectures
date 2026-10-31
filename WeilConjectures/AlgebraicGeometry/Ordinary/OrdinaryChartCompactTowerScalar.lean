/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartProperOpenScalar
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Unbounded scalar compatibility of compact-support composition

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-compact-tower-scalar).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar

private theorem properOpenScalar
    [Finite A] [Finite B] (φ : A →+* B)
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback k r p i) (E : DerivedCategoryModule A U) :
    (scalarExtension φ Z).map
        ((openImmersionLowerShriekLowerStarExchange
          (ModuleCat.{u + 1} A) sq.flip).app E) ≫
      (scalarMate φ p).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj E) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) p).map
        ((openScalarExtension φ k).hom.app E) =
    (openScalarExtension φ i).hom.app
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj E) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) i).mapDerivedCategory.map
        ((scalarMate φ r).app E) ≫
      (openImmersionLowerShriekLowerStarExchange
        (ModuleCat.{u + 1} B) sq.flip).app ((scalarExtension φ U).obj E) := by
  simpa only [properOpenCoefficientComposite, properOpenCoefficientInterchange_source,
    finiteCoefficientDirectImage_scalarMate, rightDerivedLowerStar] using
    ordinaryChartProperOpenScalar φ sq E

/-- Unbounded scalar compatibility of compact-support composition.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-compact-tower-scalar).

Proof: The intermediate compactification schemes and their restriction are Noetherian because the
relevant proper maps are of finite type over Noetherian bases.
Use the unbounded proper/open coefficient exchange square for the cartesian restriction square.
Combine it with scalar compatibility of open composition and proper direct-image composition.
The generic tower-pasting identity assembles these three squares. Expanding the specified
compact-support compositor and the open/proper coefficient maps identifies this pasted square with
the required equation. -/
theorem ordinaryChartCompactTowerScalar
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (d : Compactification g)
    (e : Compactification (f ≫ d.i)) (M : DerivedCategoryModule A X) :
    (scalarExtension φ Z).map
        ((rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app M) ≫
      (compactScalarMap φ (d.comp e)).app M =
    (compactScalarMap φ d).app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          e.restrict).obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d).map
        ((compactScalarMap φ e.restrict).app M) ≫
      (rightDerivedLowerShriekOfCompactificationCompIso B d e).hom.app
        ((scalarExtension φ X).obj M) := by
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have : IsNoetherian d.Z := ⟨⟩
  have : IsLocallyNoetherian e.Z := LocallyOfFiniteType.isLocallyNoetherian e.g
  have : CompactSpace e.Z := QuasiCompact.compactSpace_of_compactSpace e.g
  have : IsNoetherian e.Z := ⟨⟩
  have : IsLocallyNoetherian e.restrict.Z :=
    LocallyOfFiniteType.isLocallyNoetherian e.restrict.g
  have : CompactSpace e.restrict.Z := QuasiCompact.compactSpace_of_compactSpace e.restrict.g
  have : IsNoetherian e.restrict.Z := ⟨⟩
  have hi := properOpenScalar φ e.isPullback_restrict.flip
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      e.restrict.i).mapDerivedCategory.obj M)
  have ho := scalarOpen_composition_eq φ e.restrict.i (pullback.fst e.g d.i)
    e.i e.restrict_i_fst M
  have hp := scalarMate_directImage_composition_eq φ e.g d.g (e.g ≫ d.g) rfl
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (pullback.fst e.g d.i)).mapDerivedCategory.obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
          e.restrict.i).mapDerivedCategory.obj M))
  rw [right_derived_star_comp_eq, right_derived_star_comp_eq] at hp
  let aR := fun (R : Type (u + 1)) [CommRing R] ↦
    ((mapDerivedCategoryOpenImmersionLowerShriekComp
      (ModuleCat.{u + 1} R) e.restrict.i (pullback.fst e.g d.i)).symm ≪≫
      mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} R) e.restrict_i_fst).hom
  have h := tower_scalar_pasting
    (scalarExtension φ X) (scalarExtension φ e.restrict.Z) (scalarExtension φ e.Z)
    (scalarExtension φ Y) (scalarExtension φ d.Z) (scalarExtension φ Z)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A)
      (pullback.fst e.g d.i)).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) e.restrict.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) e.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) d.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) (e.g ≫ d.g))
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) e.restrict.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B)
      (pullback.fst e.g d.i)).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) e.i).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) d.i).mapDerivedCategory
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) e.restrict.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) e.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) d.g)
    (rightDerivedLowerStar (ModuleCat.{u + 1} B) (e.g ≫ d.g))
    (openScalarExtension φ e.restrict.i).hom
    (openScalarExtension φ (pullback.fst e.g d.i)).hom
    (openScalarExtension φ e.i).hom (openScalarExtension φ d.i).hom
    (scalarMate φ e.restrict.g) (scalarMate φ e.g)
    (scalarMate φ d.g) (scalarMate φ (e.g ≫ d.g))
    (aR A) (aR B)
    (openImmersionLowerShriekLowerStarExchange
      (ModuleCat.{u + 1} A) e.isPullback_restrict)
    (openImmersionLowerShriekLowerStarExchange
      (ModuleCat.{u + 1} B) e.isPullback_restrict)
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g d.g).hom
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} B) e.g d.g).hom M ho hp hi
  simpa only [rightDerivedLowerShriekOfCompactificationCompIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc, asIso_hom,
    compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj, Functor.comp_map,
    compactScalarOpen_eq, Compactification.comp, Compactification.copy,
    Compactification.postcomp, rightDerivedLowerStar, aR] using h

end AlgebraicGeometry.Etale
