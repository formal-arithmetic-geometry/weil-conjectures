/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismLocalComplex
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismLocalComplex
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismLocalReductionComparison

/-! Compatible finite reductions of the transported local complex.

## References

* Stacks Tags 06YY and 09BT
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (g : U ⟶ Y)

/-- Moving the inverses of the vertical isomorphisms across a commutative square. -/
private theorem comp_map_inv_of_comp_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B M : D} {A' B' : C} (f : A ⟶ B) (x₁ : B ⟶ M) (x₂ : M ⟶ F.obj A')
    (y : A ⟶ F.obj B') {g : B' ⟶ A'} [IsIso f] [IsIso g]
    (h : f ≫ x₁ ≫ x₂ = y ≫ F.map g) :
    x₁ ≫ x₂ ≫ F.map (inv g) = inv f ≫ y := by
  rw [IsIso.eq_inv_comp, reassoc_of% h, ← F.map_comp, IsIso.hom_inv_id, F.map_id,
    Category.comp_id]

/-- Composites of isomorphisms intertwining transitions intertwine the transitions. -/
private theorem compat_trans {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X₁ X₂ X₃ : D} {Y₁ Y₂ Y₃ : C} (t₁ : X₁ ⟶ F.obj Y₁) (t₂ : X₂ ⟶ F.obj Y₂)
    (t₃ : X₃ ⟶ F.obj Y₃) (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (a' : Y₁ ⟶ Y₂) (b' : Y₂ ⟶ Y₃)
    (ha : t₁ ≫ F.map a' = a ≫ t₂) (hb : t₂ ≫ F.map b' = b ≫ t₃) :
    t₁ ≫ F.map (a' ≫ b') = (a ≫ b) ≫ t₃ := by
  rw [F.map_comp, reassoc_of% ha, hb, Category.assoc]

/-- Relabelling along a square of functors carries intertwined transitions to intertwined
transitions. -/
private theorem relabel_compat {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂]
    [Category D₁] [Category D₂] (R : C₂ ⥤ C₁) (S₁ : C₁ ⥤ D₁) (S₂ : C₂ ⥤ D₂) (R' : D₂ ⥤ D₁)
    (σ : R ⋙ S₁ ⟶ S₂ ⋙ R') {A A' : C₁} {B B' : C₂} (t : A ⟶ R.obj B) (t' : A' ⟶ R.obj B')
    (x : A ⟶ A') (y : B ⟶ B') (h : t ≫ R.map y = x ≫ t') :
    (S₁.map t ≫ σ.app B) ≫ R'.map (S₂.map y) = S₁.map x ≫ S₁.map t' ≫ σ.app B' := by
  have hσ := σ.naturality y
  dsimp only [Functor.comp_map] at hσ
  rw [Category.assoc, ← hσ, ← Functor.map_comp_assoc, h, Functor.map_comp_assoc]

/-- The relabeled local complex computes the reductions of ordinary pullback, and
these identifications intertwine every comparable pair of levels. -/
theorem pbcIsoLocalComplex_reduction_comparison
    (K : PbcCompletedDerived Y d) (M : AdicTower Y d)
    (eK : ∀ n, M.level n ≅ (pbcCompletedReduction Y d n).obj K)
    (heK : ∀ (b a : ℕ) (hab : a ≤ b),
      adicTowerSemilinearTransition Y d M.level M.normalization b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient Y d b a hab)).map (eK a).hom =
        (eK b).hom ≫ pbcReductionTransition (pbcAdicProjection Y d b)
          (pbcAdicQuotient Y d b a hab) (pbcAdicProjection Y d a)
          (pbcAdicProjection_comp Y d b a hab) K)
    (a b : ℤ) (L : AdicTowerLocalModel d g M a b) :
    ∃ e : ∀ n : ℕ,
      (adicTowerPullback (g ≫ inv f) ((pbcAdicRings X d).obj (op n))).obj
          ((pbcReductionAdicTower X d ((completedOrdinaryPullback f d).obj K)).level n) ≅
        adicTowerLocalReduction d (g ≫ inv f) (pbcIsoLocalComplex f d g L.complex) n,
      ∀ (j i : ℕ) (hij : i ≤ j),
        adicTowerRestrictedTransition d (g ≫ inv f)
            (pbcReductionAdicTower X d ((completedOrdinaryPullback f d).obj K)) j i hij ≫
          (pbcDerivedRestrict ((adicTowerInverseImage (g ≫ inv f)).map
            (pbcAdicQuotient X d j i hij))).map (e i).hom =
        (e j).hom ≫ adicTowerLocalTransition d (g ≫ inv f)
          (pbcIsoLocalComplex f d g L.complex) j i hij := by
  classical
  let h := g ≫ inv f
  let Lh := adicTowerInverseImage h
  let Lg := adicTowerInverseImage g
  let ψ := pbcIsoLocalCoefficient f d g
  let κ := pbcIsoLevelCoefficient f d g
  let K' := (completedOrdinaryPullback f d).obj K
  let PK := (adicTowerPullback g (pbcAdicCompletion Y d)).obj K
  let QC := DerivedCategory.Q.obj L.complex
  obtain ⟨Φ⟩ := pbcIsoLocalPullback_nonempty f d g K
  let G (n : ℕ) : (pbcDerivedExtend (Lg.map (pbcAdicProjection Y d n))).obj PK ≅
      (pbcDerivedExtend (Lg.map (pbcAdicProjection Y d n))).obj QC :=
    ((pbcPullbackExtendIso g (pbcAdicProjection Y d n)).app K).symm ≪≫
    (adicTowerPullback g ((pbcAdicRings Y d).obj (op n))).mapIso (eK n).symm ≪≫
    L.identification n
  let β (n : ℕ) (Z : DerivedCategory (pbcModules U (Lg.obj (pbcAdicCompletion Y d)))) :=
    asIso ((pbcRelabelExtend ψ (κ n) _ _ (pbcIsoLevelCoefficient_comm f d g n)).app Z)
  refine ⟨fun n ↦ (pbcPullbackExtendIso h (pbcAdicProjection X d n)).app K' ≪≫
    (pbcDerivedExtend (Lh.map (pbcAdicProjection X d n))).mapIso Φ ≪≫ β n PK ≪≫
    (pbcDerivedRestrict (κ n).hom).mapIso (G n) ≪≫ (β n QC).symm ≪≫
    (pbcDerivedExtend (Lh.map (pbcAdicProjection X d n))).mapIso
      ((pbcRestrict ψ.hom).mapDerivedCategoryFactors.app L.complex), fun j i hij ↦ ?_⟩
  let q := pbcAdicQuotient X d j i hij
  let qY := pbcAdicQuotient Y d j i hij
  have hq : Lh.map (pbcAdicProjection X d j) ≫ Lh.map q =
      Lh.map (pbcAdicProjection X d i) := by
    rw [← Functor.map_comp, pbcAdicProjection_comp]
  have hqY : Lg.map (pbcAdicProjection Y d j) ≫ Lg.map qY =
      Lg.map (pbcAdicProjection Y d i) := by
    rw [← Functor.map_comp, pbcAdicProjection_comp]
  have hN : adicTowerSemilinearTransition X d (pbcReductionAdicTower X d K').level
      (pbcReductionAdicTower X d K').normalization j i hij =
        pbcReductionTransition (pbcAdicProjection X d j) q (pbcAdicProjection X d i)
          (pbcAdicProjection_comp X d j i hij) K' := by
    dsimp only [pbcReductionAdicTower, adicTowerSemilinearTransition, pbcReductionNormalization,
      pbcReductionNormalizationHom, asIso_hom]
    exact ((pbcDerivedScalarAdjunction q).homEquiv _ _).apply_symm_apply _
  have h1 := pbcPullbackExtendIso_transition h (pbcAdicProjection X d j) q
    (pbcAdicProjection X d i) (pbcAdicProjection_comp X d j i hij) K'
  have h2 := pbcReductionTransition_naturality (Lh.map (pbcAdicProjection X d j)) (Lh.map q)
    (Lh.map (pbcAdicProjection X d i)) hq Φ.hom
  have h3 (Z : DerivedCategory (pbcModules U (Lg.obj (pbcAdicCompletion Y d)))) :=
    pbcRelabelExtend_transition ψ (κ j) (κ i) (Lh.map (pbcAdicProjection X d j)) (Lh.map q)
      (Lh.map (pbcAdicProjection X d i)) hq (Lg.map (pbcAdicProjection Y d j)) (Lg.map qY)
      (Lg.map (pbcAdicProjection Y d i)) hqY (pbcIsoLevelCoefficient_comm f d g j)
      (pbcIsoLevelCoefficient_quotient f d g j i hij) (pbcIsoLevelCoefficient_comm f d g i) Z
  have h8 := pbcReductionTransition_naturality (Lh.map (pbcAdicProjection X d j)) (Lh.map q)
    (Lh.map (pbcAdicProjection X d i)) hq
    ((pbcRestrict ψ.hom).mapDerivedCategoryFactors.hom.app L.complex)
  have hG : pbcReductionTransition (Lg.map (pbcAdicProjection Y d j)) (Lg.map qY)
        (Lg.map (pbcAdicProjection Y d i)) hqY PK ≫
        (pbcDerivedRestrict (Lg.map qY)).map (G i).hom =
      (G j).hom ≫ adicTowerLocalTransition d g L.complex j i hij := by
    have hg1 := pbcPullbackExtendIso_transition g (pbcAdicProjection Y d j) qY
      (pbcAdicProjection Y d i) (pbcAdicProjection_comp Y d j i hij) K
    have hρ := (proEtaleRingRestrictionDerivedPullback g _ _ _ _ qY (Lg.map qY) (Iso.refl _)
      (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm)).inv.naturality
        (eK i).inv
    have hs : adicTowerSemilinearTransition Y d M.level M.normalization j i hij =
        (eK j).hom ≫ pbcReductionTransition (pbcAdicProjection Y d j) qY
          (pbcAdicProjection Y d i) (pbcAdicProjection_comp Y d j i hij) K ≫
          (pbcDerivedRestrict qY).map (eK i).inv := by
      rw [← reassoc_of% heK j i hij, ← Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
    dsimp only [Functor.comp_map] at hρ
    have key : pbcReductionTransition (Lg.map (pbcAdicProjection Y d j)) (Lg.map qY)
          (Lg.map (pbcAdicProjection Y d i)) hqY PK ≫
          (pbcDerivedRestrict (Lg.map qY)).map
            ((pbcPullbackExtendIso g (pbcAdicProjection Y d i)).inv.app K) ≫
          (pbcDerivedRestrict (Lg.map qY)).map
            ((adicTowerPullback g ((pbcAdicRings Y d).obj (op i))).map (eK i).inv) =
        (pbcPullbackExtendIso g (pbcAdicProjection Y d j)).inv.app K ≫
          (adicTowerPullback g ((pbcAdicRings Y d).obj (op j))).map (eK j).inv ≫
          adicTowerRestrictedTransition d g M j i hij := by
      dsimp only [Lg, PK]
      rw [← cancel_epi ((pbcPullbackExtendIso g (pbcAdicProjection Y d j)).hom.app K),
        Iso.hom_inv_id_app_assoc, ← reassoc_of% hg1, ← Functor.map_comp_assoc,
        Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id]
      simp only [Category.id_comp]
      dsimp only [adicTowerRestrictedTransition]
      rw [hs, Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
      simp only [Category.id_comp]
      congr 1
      exact hρ.symm
    dsimp only [G, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
      Iso.app_inv]
    simp only [Functor.map_comp, Category.assoc]
    rw [← L.compatible j i hij, reassoc_of% key]
  let σq := pbcDerivedRestrictSquare (κ j).hom (κ i).hom (Lh.map q) (Lg.map qY)
    (pbcIsoLevelCoefficient_quotient f d g j i hij)
  have hrel := relabel_compat _ _ _ _ σq.hom _ _ _ _ hG
  have h7 := comp_map_inv_of_comp_map (pbcDerivedRestrict (Lh.map q)) _ _ _ _ (h3 QC)
  refine compat_trans (pbcDerivedRestrict (Lh.map q)) _
    (pbcReductionTransition (Lh.map (pbcAdicProjection X d j)) (Lh.map q)
      (Lh.map (pbcAdicProjection X d i)) hq
      ((adicTowerPullback h (pbcAdicCompletion X d)).obj K')) _ _ _ _ _ ?_ ?_
  · dsimp only [adicTowerRestrictedTransition]
    rw [hN, Category.assoc]
    exact h1
  refine compat_trans (pbcDerivedRestrict (Lh.map q)) _
    (pbcReductionTransition (Lh.map (pbcAdicProjection X d j)) (Lh.map q)
      (Lh.map (pbcAdicProjection X d i)) hq ((pbcDerivedRestrict ψ.hom).obj PK))
    _ _ _ _ _ h2.symm ?_
  refine compat_trans (pbcDerivedRestrict (Lh.map q)) _ ((pbcDerivedRestrict (κ j).hom).map
    (pbcReductionTransition (Lg.map (pbcAdicProjection Y d j)) (Lg.map qY)
      (Lg.map (pbcAdicProjection Y d i)) hqY PK) ≫ σq.hom.app _) _ _ _ _ _ (h3 PK).symm ?_
  refine compat_trans (pbcDerivedRestrict (Lh.map q)) _ ((pbcDerivedRestrict (κ j).hom).map
    (pbcReductionTransition (Lg.map (pbcAdicProjection Y d j)) (Lg.map qY)
      (Lg.map (pbcAdicProjection Y d i)) hqY QC) ≫ σq.hom.app _) _ _ _ _ _ hrel ?_
  refine compat_trans (pbcDerivedRestrict (Lh.map q)) _
    (pbcReductionTransition (Lh.map (pbcAdicProjection X d j)) (Lh.map q)
      (Lh.map (pbcAdicProjection X d i)) hq ((pbcDerivedRestrict ψ.hom).obj QC))
    _ _ _ _ _ ?_ h8.symm
  rw [Category.assoc]
  exact h7

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {Λ Λ' Λ'' : ScalarSixRing.{u}} {X Y U : Scheme.{u}}

/-- The normalized scalar comparison data. Its `thetaNormalization` fixes every hom
component to `scalarSixPullHom`, hence fixes its inverse and the entire data uniquely.
This choice therefore selects no arbitrary comparison. -/
def pbcLocalScalarData : ScalarSixPullbackData.{u} :=
  Classical.choice scalarSixPullbackData_exists

/-- The specified local coefficient comparison: inverse geometric compositor, inverse
scalar comparison, and scalar extension of the given local identification. -/
def pbcLocalReductionComparison (a : Λ ⟶ Λ') (f : X ⟶ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    {N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
    (e : (scalarSixPull Λ (h ≫ f)).obj K ≅ N) :
    (scalarSixPull Λ' h).obj ((scalarSixPull Λ' f).obj ((scalarSixChange a Y).obj K)) ≅
      (scalarSixChange a U).obj N :=
  ((scalarSixPullComp Λ' h f).app ((scalarSixChange a Y).obj K)).symm ≪≫
    ((pbcLocalScalarData.theta a (h ≫ f)).app K).symm ≪≫
      (scalarSixChange a U).mapIso e

/-- The comparison between a composite scalar change and successive local changes. -/
def pbcLocalReductionTower (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'') (f : X ⟶ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixPull Λ'' h).obj
        ((scalarSixPull Λ'' f).obj ((scalarSixChange (a ≫ b) Y).obj K)) ≅
      (scalarSixChange b U).obj
        ((scalarSixPull Λ' h).obj ((scalarSixPull Λ' f).obj ((scalarSixChange a Y).obj K))) :=
  (scalarSixPull Λ'' f ⋙ scalarSixPull Λ'' h).mapIso
      ((scalarSixTower a b Y).app K).symm ≪≫
    (scalarSixPull Λ'' h).mapIso
      ((pbcLocalScalarData.theta b f).app ((scalarSixChange a Y).obj K)).symm ≪≫
    ((pbcLocalScalarData.theta b h).app
      ((scalarSixPull Λ' f).obj ((scalarSixChange a Y).obj K))).symm

private theorem local_composition (a : Λ ⟶ Λ') (f : X ⟶ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixPullComp Λ' h f).inv.app ((scalarSixChange a Y).obj K) ≫
        (pbcLocalScalarData.theta a (h ≫ f)).inv.app K =
      (scalarSixPull Λ' h).map ((pbcLocalScalarData.theta a f).inv.app K) ≫
        (pbcLocalScalarData.theta a h).inv.app ((scalarSixPull Λ f).obj K) ≫
          (scalarSixChange a U).map ((scalarSixPullComp Λ h f).inv.app K) := by
  have q := IsIso.inv_eq_inv.mpr (pbcLocalScalarData.composition a h f K)
  simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
    Category.assoc] using q

/-- The specified local comparison equals the iterated inverse-image/scalar comparison. -/
theorem pbcLocalReductionComparison_iterated (a : Λ ⟶ Λ') (f : X ⟶ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    {N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
    (e : (scalarSixPull Λ (h ≫ f)).obj K ≅ N) :
    (pbcLocalReductionComparison a f h K e).hom =
      (scalarSixPull Λ' h).map ((pbcLocalScalarData.theta a f).inv.app K) ≫
        (pbcLocalScalarData.theta a h).inv.app ((scalarSixPull Λ f).obj K) ≫
          (scalarSixChange a U).map ((scalarSixPullComp Λ h f).inv.app K ≫ e.hom) := by
  dsimp only [pbcLocalReductionComparison, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [← Category.assoc, local_composition]
  simp only [Functor.map_comp, Category.assoc]

/-- Naturality in the specified local identification. -/
theorem pbcLocalReductionComparison_naturality (a : Λ ⟶ Λ') (f : X ⟶ Y) (h : U ⟶ X)
    {K K' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)}
    {N N' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
    (e : (scalarSixPull Λ (h ≫ f)).obj K ≅ N)
    (e' : (scalarSixPull Λ (h ≫ f)).obj K' ≅ N') (v : K ⟶ K') (w : N ⟶ N')
    (he : e.hom ≫ w = (scalarSixPull Λ (h ≫ f)).map v ≫ e'.hom) :
    (pbcLocalReductionComparison a f h K e).hom ≫ (scalarSixChange a U).map w =
      (scalarSixPull Λ' h).map ((scalarSixPull Λ' f).map ((scalarSixChange a Y).map v)) ≫
        (pbcLocalReductionComparison a f h K' e').hom := by
  dsimp only [pbcLocalReductionComparison, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [← Functor.map_comp, he, Functor.map_comp]
  have q := (pbcLocalScalarData.theta a (h ≫ f)).inv.naturality v
  dsimp only [Functor.comp_map] at q
  rw [← reassoc_of% q]
  have r := (scalarSixPullComp Λ' h f).inv.naturality ((scalarSixChange a Y).map v)
  dsimp only [Functor.comp_map] at r
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ (pbcLocalScalarData.theta a (h ≫ f)).inv.app K' ≫
      (scalarSixChange a U).map e'.hom) r.symm

/-- Scalar-tower compatibility of the local comparison, for arbitrary coefficient maps. -/
theorem pbcLocalReductionComparison_tower (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    (f : X ⟶ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    {N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
    (e : (scalarSixPull Λ (h ≫ f)).obj K ≅ N) :
    (pbcLocalReductionComparison (a ≫ b) f h K e).hom =
      (pbcLocalReductionTower a b f h K).hom ≫
        (scalarSixChange b U).map (pbcLocalReductionComparison a f h K e).hom ≫
          (scalarSixTower a b U).hom.app N := by
  have q := IsIso.inv_eq_inv.mpr (pbcLocalScalarData.tower a b (h ≫ f) K)
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
    Category.assoc] at q
  dsimp only [pbcLocalReductionComparison, pbcLocalReductionTower, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (local_composition b f h ((scalarSixChange a Y).obj K))]
  rw [reassoc_of% ((scalarSixPullComp Λ'' h f).inv.naturality
    ((scalarSixTower a b Y).inv.app K))]
  rw [← reassoc_of% q]
  have r := (scalarSixTower a b U).hom.naturality e.hom
  dsimp only [Functor.comp_map] at r
  rw [r]
  simp only [Iso.inv_hom_id_app_assoc]

/-- Natural local coefficient change under isomorphism transport, with its iterated
formula and scalar-tower coherence. The local map is parametrized as `h: U ⟶ X`;
for a map `g: U ⟶ Y`, take `h = g ≫ f.inv`, since `h ≫ f.hom = g`. -/
theorem pbcIsoLocalComplex_reduction_comparison (a : Λ ⟶ Λ') (f : X ≅ Y) (h : U ⟶ X)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    {N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
    (e : (scalarSixPull Λ (h ≫ f.hom)).obj K ≅ N) :
    (pbcLocalReductionComparison a f.hom h K e).hom =
        (scalarSixPull Λ' h).map ((pbcLocalScalarData.theta a f.hom).inv.app K) ≫
          (pbcLocalScalarData.theta a h).inv.app ((scalarSixPull Λ f.hom).obj K) ≫
            (scalarSixChange a U).map
              ((scalarSixPullComp Λ h f.hom).inv.app K ≫ e.hom) ∧
      (∀ {K' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)}
        {N' : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U)}
        (e' : (scalarSixPull Λ (h ≫ f.hom)).obj K' ≅ N') (v : K ⟶ K') (w : N ⟶ N'),
        e.hom ≫ w = (scalarSixPull Λ (h ≫ f.hom)).map v ≫ e'.hom →
          (pbcLocalReductionComparison a f.hom h K e).hom ≫ (scalarSixChange a U).map w =
            (scalarSixPull Λ' h).map
                ((scalarSixPull Λ' f.hom).map ((scalarSixChange a Y).map v)) ≫
              (pbcLocalReductionComparison a f.hom h K' e').hom) ∧
      (∀ {Λ'' : ScalarSixRing.{u}} (b : Λ' ⟶ Λ''),
        (pbcLocalReductionComparison (a ≫ b) f.hom h K e).hom =
          (pbcLocalReductionTower a b f.hom h K).hom ≫
            (scalarSixChange b U).map (pbcLocalReductionComparison a f.hom h K e).hom ≫
              (scalarSixTower a b U).hom.app N) := by
  exact ⟨pbcLocalReductionComparison_iterated a f.hom h K e,
    fun e' v w he ↦ pbcLocalReductionComparison_naturality a f.hom h e e' v w he,
    fun b ↦ pbcLocalReductionComparison_tower a b f.hom h K e⟩

end AlgebraicGeometry.ProEtale.CondensedRing
