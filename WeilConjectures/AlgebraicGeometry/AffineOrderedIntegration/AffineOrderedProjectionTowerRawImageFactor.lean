/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedProjectionTower
import all WeilConjectures.AlgebraicGeometry.CartesianTower.CartesianTowerRestriction
import all WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientOrdinaryClopenLocalization
import all WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization

/-! Factorization of the raw proper/open tower through the normalized tower formula.

Source: Stacks 0F7J, proper/open site normalization.
(blueprint: lem-pur-affine-projection-tower-raw-image-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

private theorem left_comp_target
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {M : D ⥤ E} {S : E ⥤ D}
    {N : C ⥤ E} {T : E ⥤ C}
    (a : L ⊣ R) (b : M ⊣ S) (c : N ⊣ T) (η : T ≅ S ⋙ R) :
    Adjunction.leftAdjointCompIso a b c η.symm =
      (a.comp b).leftAdjointUniq (c.ofNatIsoRight η) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ((a.comp b).homEquiv K _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  apply (cancel_mono (η.inv.app (N.obj K))).mp
  change _ = (c.unit.app K ≫ η.hom.app (N.obj K)) ≫ η.inv.app (N.obj K)
  calc
    _ = c.unit.app K := by
      simpa only [Iso.symm_hom] using
        WeilConjectures.AmbientCompositor.left_comp_unit a b c η.symm K
    _ = _ := by
      rw [Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id (c.unit.app K)).symm

private theorem open_comp_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V Z : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    properOpenShriekComp A j b = towerOpenComposition A j b := by
  rw [← AmbientClopen.ordinary_open_comp_localized]
  unfold towerOpenComposition AmbientClopen.openComp AmbientClopen.sheafOpenComp
  rw [left_comp_target]

private theorem open_congr_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {U Z : Scheme.{u}} {j k : U ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    properOpenShriekCongr A h = towerOpenCongr A h := by
  subst k
  exact AmbientClopen.proper_open_congr_refl A j

/-- On a comparison image, the raw map is the normalized tower word.
Source: proper/open mate normalization, derived direct-image composition, and
open-extension composition.
(blueprint: lem-pur-affine-projection-tower-raw-image-factor).
-/
theorem projection_tower_raw_image_factor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian T] [IsNoetherian Y]
    (f : X ⟶ T) (g : T ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (b : Compactification g) (e : Compactification (f ≫ b.i))
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hLambda : IsIso (towerLambda A (pullback.fst e.g b.i) b.i e.restrict.g e.g
      e.isPullback_restrict.w.symm
      ((towerJ A e.restrict.i).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj)))) :
    projectionTowerMap A b e
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) =
      (towerP A b.g).map
          (towerGamma A (pullback.fst e.g b.i) b.i e.restrict.g e.g
            e.isPullback_restrict.w.symm
            ((towerJ A e.restrict.i).obj
              ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj))
            hLambda) ≫
        (finiteDirectImageComposition A e.g b.g).inv.app
          ((towerJ A (pullback.fst e.g b.i)).obj
            ((towerJ A e.restrict.i).obj
              ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj))) ≫
        (towerP A (e.g ≫ b.g)).map
      (((towerOpenComposition A e.restrict.i (pullback.fst e.g b.i) ≪≫
            towerOpenCongr A e.restrict_i_fst).hom.app
              ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj))) := by
  let := hLambda
  unfold projectionTowerMap
  rw [AlgebraicGeometry.ProEtale.raw_mate_gamma
    A (pullback.fst e.g b.i) b.i e.restrict.g e.g
    e.isPullback_restrict.flip
    ((towerJ A e.restrict.i).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj)) hLambda]
  rw [open_comp_eq, open_congr_eq]
  rfl

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
