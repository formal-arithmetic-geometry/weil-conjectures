/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Sites.Adjunction

/-! # Canonical coefficient comparison for constant-module sections

Source: Stacks Project, Tags 03DB, 03CO and 09Z1.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Forget the scalar action and compare constant sheaves, then undo the canonical
constant-sheaf pullback comparison. This uses actual natural isomorphisms, not a choice
of an equivalence family. -/
noncomputable def constantModuleSectionCoefficientSheafIso
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X Z : Scheme.{u}} (f : Z ⟶ X) :
    (sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≅
      (upperStar AddCommGrpCat.{u + 1} f).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)) := by
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let r : ℤ →+* Λ := Int.castRingHom Λ
  let R := ModuleCat.restrictScalars.{u + 1} r
  let T := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : R.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} r).isLeftAdjoint
  have : V.IsLeftAdjoint := inferInstanceAs (R ⋙ T).IsLeftAdjoint
  have : Z.smallEtaleTopology.PreservesSheafification V :=
    Sheaf.preservesSheafification_of_adjunction _
      (Adjunction.ofIsLeftAdjoint V)
  exact (constantCommuteCompose Z.smallEtaleTopology V).app M ≪≫
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app (V.obj M)).symm

/-- Evaluate the coefficient comparison at the base change of the étale object. -/
noncomputable def constantModuleSectionCoefficientEquiv
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X Z : Scheme.{u}} (U : X.Etale) (f : Z ⟶ X) :
    ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj
        (op U) ≃+
    ((lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M)))).obj.obj
        (op U) :=
  Iso.addCommGroupIsoToAddEquiv
    (((sheafSections Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (f.Etale.obj U))).mapIso (constantModuleSectionCoefficientSheafIso Λ M f))

/-- The canonical coefficient comparison intertwines module transitions with the
adjunction-unit transition for the abelian sheaf pulled back from the base.

Source: Stacks Project, Tags 03DB and 03CO (forgetting coefficients and sheafification),
and Tag 09Z1 (canonical transition maps).
(blueprint: lem-weil-pbc-constant-module-section-coefficients).

Proof: Write C_X for the constant abelian sheaf on X. The sheaf isomorphism used here
is the constantCommuteCompose comparison followed by the inverse of the canonical
constant-sheaf pullback comparison. The former commutes with sheafification generators.
The latter is the uniqueness isomorphism of left adjoints to terminal evaluation, so
its adjoint sends each constant generator to the same generator. Naturality of the
inverse-image unit moves the coefficient comparison across the unit. The unit equation
for uniqueness of left adjoints identifies the composite constant pullback comparison
with upperStarComp. Applying lowerStar and its composition isomorphism gives the
sheaf-level commuting square. Evaluate it at U. Direct image is precomposition on
étale objects, so coefficient forgetting commutes with it definitionally. This gives
the displayed section equality. There are no restrictions on coefficients or schemes;
zero coefficients and empty pullbacks use the same unit and naturality equations. -/
theorem constantModuleSectionCoefficientEquiv_naturality
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} (U : X.Etale)
    {Z W : Scheme.{u}} (g : W ⟶ Z) (f : Z ⟶ X) (h : W ⟶ X)
    (w : g ≫ f = h)
    (z : ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj.obj
        (op U)) :
    let A := AddCommGrpCat.{u + 1}
    let G := (constantSheaf X.smallEtaleTopology A).obj
      ((forget₂ (ModuleCat.{u + 1} Λ) A).obj M)
    constantModuleSectionCoefficientEquiv Λ M U h
        ((constantModulePushforwardMap Λ M f h g w).hom.app (op U) z) =
      ((lowerStar A f).map
          ((upperStarLowerStarAdjunction A g).unit.app ((upperStar A f).obj G)) ≫
        (lowerStarComp A g f h w.symm).hom.app _ ≫
        (lowerStar A h).map ((upperStarComp A g f h w.symm).inv.app G)).hom.app
          (op U) (constantModuleSectionCoefficientEquiv Λ M U f z) := by
  sorry

end AlgebraicGeometry.Etale
