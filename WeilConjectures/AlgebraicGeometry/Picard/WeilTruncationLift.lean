/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OperationComparisons.CondensedOperationComparisons
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PodCondensedAutomorphismCompactExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.SmoothPurity.WeilVerdierModuleConstructibilityComparison
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.CategoryTheory.NormalizedClosedExchange.NormalizedClosedAdjunctionExchange
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-! Six operations on Weil complexes, with their prescribed normalized comparisons.
Source: prop-weil-operations and its five-step proof. (blueprint: prop-weil-operations). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v uA vA uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory DerivedCategory.monoidalClosed

namespace WeilConjectures

private theorem woEquivariant_of_square
    {C : Type uC} [Category.{vC} C] (P : C ⥤ C)
    {A B : C} (θA : P.obj A ⟶ A) (θB : P.obj B ⟶ B) (a : A ⟶ B)
    (h : P.map a ≫ θB = θA ≫ a) : WOEquivariant P θA θB a := by
  refine ⟨h, ?_⟩
  intro ha
  let := ha
  apply (cancel_mono a).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc, ← P.map_comp, IsIso.inv_hom_id,
    P.map_id, Category.id_comp]


set_option maxHeartbeats 1600000 in
-- The proof transports the full native derived truncation triangle.
/-- The standard truncation maps and connecting arrow commute with the induced
Weil structures. Source: prop-weil-operations.proof.md, truncation paragraph.
(blueprint: lem-wo-truncation-lift).

Proof: restrict the exact automorphism to the constructible category and use the
ordinary induced t-structure. Exactness identifies its aisles with the ordinary
cohomological bounds. The t-exact truncation comparisons are uniquely fixed by
counit and unit. Naturality proves equivariance of these two maps. The functorial
truncation-triangle identity and naturality of its connecting transformation prove
equivariance of the connecting arrow. The restriction comparison commutes with
integer shifts, so this is the original triangle after forgetting. -/
theorem woTruncations_of_standard
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (g : X ⟶ X) [IsIso g]
    [(boundedConstructible (condensedRingObj Λ X)).IsTriangulated]
    (t : TStructure (BoundedConstructible (condensedRingObj Λ X)))
    (ht : OrdinaryConstructibleTruncations (condensedRingObj Λ X) t) :
    WOTruncations Λ X g := by
  let R := condensedRingObj Λ X
  let p := boundedConstructible R
  let P := (upperStar Λ g).mapDerivedCategory
  have hP (K : BoundedConstructible R) : p (P.obj K.obj) := by
    exact p.prop_of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).app K.obj)
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ g K.obj K.property)
  let Q := p.lift (p.ι ⋙ P) hP
  have : Q.IsTriangulated := inferInstance
  have : Q.IsTExact t t := by
    constructor
    · intro K n hK
      apply (ht.1 _ n).mpr
      have : K.obj.IsLE n := (ht.1 _ n).mp hK
      exact (upperStar Λ g).isLE_mapDerivedCategory_obj K.obj n
    · intro K n hK
      apply (ht.2.1 _ n).mpr
      have : K.obj.IsGE n := (ht.2.1 _ n).mp hK
      exact (upperStar Λ g).isGE_mapDerivedCategory_obj K.obj n
  have hb : t.bounded = ⊤ := top_unique (fun K _ ↦ ht.2.2.1 K)
  have hcomp : ConstructibleTruncationCompatibility t t Q := by
    constructor
    · intro m
      have hh := t.texact_truncation_comparison.{u + 2, u + 1, u + 2, u + 1, u + 2, u + 1}
        t hb hb Q m
      exact ⟨⟨Q.eTruncLTIso t t (m + 1 : ℤ), fun K ↦ (hh.1 K).1,
        fun a ha ↦ hh.2.1 a ha⟩,
        ⟨Q.eTruncGEIso t t m, fun K ↦ (hh.1 K).2, fun a ha ↦ hh.2.2.1 a ha⟩⟩
    · intro i
      exact ⟨Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Q.commShiftIso i) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _ (Q.eTruncGEIso t t i) ≪≫
            (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (Q.eTruncLTIso t t (i + 1 : ℤ)) _ ≪≫
            Functor.associator _ _ _) _ ≪≫ Functor.associator _ _ _⟩
  refine ⟨inferInstance, condensedConstructibleTruncations_pullback Λ g, hP,
    t, ht, hcomp, (fun m ↦ Q.eTruncLTIso t t (m + 1 : ℤ)),
    (fun m ↦ Q.eTruncGEIso t t m), inferInstance, ?_, ?_⟩
  · intro K
    have hh := NatTrans.shift_app_comm ((p.liftCompιIso (p.ι ⋙ P) hP).hom)
      (1 : ℤ) K
    have he : p.ι.map ((Q.commShiftIso (1 : ℤ)).hom.app K) ≫
        (p.ι.commShiftIso (1 : ℤ)).hom.app (Q.obj K) =
        P.map ((p.ι.commShiftIso (1 : ℤ)).hom.app K) ≫
          (P.commShiftIso (1 : ℤ)).hom.app K.obj := by
      simpa [Functor.commShiftIso_comp_hom_app, ObjectProperty.liftCompιIso] using hh
    simpa only [Category.assoc, Iso.app_inv] using
      (Iso.eq_comp_inv ((p.ι.commShiftIso (1 : ℤ)).app (Q.obj K))).mpr he
  · intro m
    have hh := t.texact_truncation_comparison.{u + 2, u + 1, u + 2, u + 1, u + 2, u + 1}
        t hb hb Q m
    refine ⟨fun K ↦ (hh.1 K).1, fun K ↦ (hh.1 K).2, ?_⟩
    have hcLE (K) :
        (Q.eTruncLTIso t t (m + 1 : ℤ)).hom.app K ≫ (t.truncLEι m).app (Q.obj K) =
          Q.map ((t.truncLEι m).app K) := (hh.1 K).1
    intro K
    refine ⟨woEquivariant_of_square Q _ _ _ ?_,
      woEquivariant_of_square Q _ _ _ ?_, woEquivariant_of_square Q _ _ _ ?_⟩
    · change Q.map ((t.truncLEι m).app K.carrier) ≫ K.str.hom =
        ((Q.eTruncLTIso t t (m + 1 : ℤ)).hom.app K.carrier ≫
          (t.truncLE m).map K.str.hom) ≫ (t.truncLEι m).app K.carrier
      rw [Category.assoc, (t.truncLEι m).naturality, ← Category.assoc, hcLE]
      rfl
    · change Q.map ((t.truncGEπ m).app K.carrier) ≫
        ((Q.eTruncGEIso t t m).hom.app K.carrier ≫ (t.truncGE m).map K.str.hom) =
        K.str.hom ≫ (t.truncGEπ m).app K.carrier
      rw [← Category.assoc, (hh.1 _).2]
      exact ((t.truncGEπ m).naturality K.str.hom).symm
    · change Q.map ((t.truncGEδLE m (m + 1) rfl).app K.carrier) ≫
        ((Q.commShiftIso (1 : ℤ)).hom.app ((t.truncLE m).obj K.carrier) ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((Q.eTruncLTIso t t (m + 1 : ℤ)).hom.app K.carrier ≫
              (t.truncLE m).map K.str.hom)) =
        ((Q.eTruncGEIso t t (m + 1 : ℤ)).hom.app K.carrier ≫
          (t.truncGE (m + 1)).map K.str.hom) ≫
          (t.truncGEδLE m (m + 1) rfl).app K.carrier
      have hd := Q.eTruncGEδLT_comm t t (m + 1 : ℤ) K.carrier
      have hd' : Q.map ((t.truncGEδLE m (m + 1) rfl).app K.carrier) ≫
          (Q.commShiftIso (1 : ℤ)).hom.app ((t.truncLE m).obj K.carrier) ≫
          (shiftFunctor _ (1 : ℤ)).map
            ((Q.eTruncLTIso t t (m + 1 : ℤ)).hom.app K.carrier) =
        (Q.eTruncGEIso t t (m + 1 : ℤ)).hom.app K.carrier ≫
          (t.truncGEδLE m (m + 1) rfl).app (Q.obj K.carrier) := by
        simpa [TStructure.truncGEδLE, TStructure.truncLEIsoTruncLT, TStructure.truncLE] using hd
      calc
        _ = ((Q.eTruncGEIso t t (m + 1 : ℤ)).hom.app K.carrier ≫
              (t.truncGEδLE m (m + 1) rfl).app (Q.obj K.carrier)) ≫
              (shiftFunctor _ (1 : ℤ)).map ((t.truncLE m).map K.str.hom) := by
          simpa only [TStructure.truncLE, Functor.map_comp, Category.assoc] using
            congrArg (fun z ↦ z ≫ (shiftFunctor _ (1 : ℤ)).map
              ((t.truncLE m).map K.str.hom)) hd'
        _ = _ := by
          simpa only [Functor.comp_map, Category.assoc] using
            congrArg (fun z ↦ (Q.eTruncGEIso t t (m + 1 : ℤ)).hom.app K.carrier ≫ z)
              ((t.truncGEδLE m (m + 1) rfl).naturality K.str.hom).symm
end WeilConjectures
