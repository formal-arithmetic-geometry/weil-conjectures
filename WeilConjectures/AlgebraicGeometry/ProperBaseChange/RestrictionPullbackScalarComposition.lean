/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Coherence of restriction and pullback for successive coefficient maps

Source: Stacks Project, Tags 03EL and 06YY.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry.Scheme

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso
  comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  proEtaleRingModulePullback proEtaleRingModuleAdjunction

private theorem mate_naturality
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R')
    {G G' : C ⥤ E} {H H' : D ⥤ F}
    (μ : TwoSquare G L L' H) (ν : TwoSquare G' L L' H')
    (p : G ⟶ G') (q : H ⟶ H')
    (h : ∀ N, p.app (R.obj N) ≫ (mateEquiv a b ν).app N =
      (mateEquiv a b μ).app N ≫ R'.map (q.app N)) (M : C) :
    L'.map (p.app M) ≫ ν.app M = μ.app M ≫ q.app (L.obj M) := by
  change G ⋙ L' ⟶ L ⋙ H at μ
  change G' ⋙ L' ⟶ L ⋙ H' at ν
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := b.unit.naturality (p.app M)
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [← reassoc_of% hu]
  have hν := unit_mateEquiv a b ν M
  have hμ := unit_mateEquiv a b μ M
  dsimp only [Functor.id_obj] at hν hμ
  rw [← hν, ← reassoc_of% hμ]
  rw [← p.naturality_assoc]
  exact congrArg (fun z ↦ G.map (a.unit.app M) ≫ z) (h (L.obj M))

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
    (RX SX TX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY SY TY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (aX : RX ⟶ SX) (bX : SX ⟶ TX) (cX : RX ⟶ TX) (hX : aX ≫ bX = cX)
    (aY : RY ⟶ SY) (bY : SY ⟶ TY) (cY : RY ⟶ TY) (hY : aY ≫ bY = cY)
    (eR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RX ≅ RY)
    (eS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SX ≅ SY)
    (eT : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj TX ≅ TY)
    (ha : eR.hom ≫ aY =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aX ≫ eS.hom)
    (hb : eS.hom ≫ bY =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map bX ≫ eT.hom)
    (hc : eR.hom ≫ cY =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map cX ≫ eT.hom)

end AlgebraicGeometry.Scheme
