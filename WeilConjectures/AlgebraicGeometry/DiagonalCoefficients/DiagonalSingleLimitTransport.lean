/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernCoefficientPullback

/-! # Transport of a single-limit source along a whole-tower comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory

/-- The exact single comparison followed by the single of an ordinary morphism.
Source: blueprint diagonal coefficient changes (3), exact-single compatibility.
(blueprint: lem-diagonal-single-limit-transport).
Construction: compose the exact single comparison with the single of the given map. -/
def diagonalSingleEndpointMap
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [hA : HasDerivedCategory A] [hB : HasDerivedCategory B]
    (P : A ⥤ B) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {X : A} {Y : B} (v : P.obj X ⟶ Y) :
    P.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj X) ⟶
      (DerivedCategory.singleFunctor B 0).obj Y :=
  (P.mapDerivedCategorySingleFunctor 0).hom.app X ≫
    (DerivedCategory.singleFunctor B 0).map v

set_option maxHeartbeats 2000000 in
-- The full-cone calculation unfolds nested derived-category comparison functors.
/-- Ordinary cone transport and the normalized full-cone mate give single-limit transport.

Source: blueprint latest, diagonal coefficient changes (3), transpose of the source cone.
(blueprint: lem-diagonal-single-limit-transport).

Proof: naturality of the derived-limit comparison moves the inverse of the source
single identification through the mate. Cancel the two single identifications in
the supplied whole-system endpoint equation. Apply the full-cone mate equation,
then naturality of the ordinary cone-to-derived-limit map to the ordinary cone
square. Compatibility of exact localization with the single embedding gives the
scalar square, and naturality of that embedding gives the prescribed ordinary
source map. All equalities are in the derived category of strict systems before
applying the limit; no termwise evaluation is used. -/
theorem diagonalSingleLimit_transport
    {A B C D : Type*}
    [Category A] [Abelian A] [Category B] [Abelian B]
    [Category C] [Abelian C] [Category D] [Abelian D]
    [hA : HasDerivedCategory A] [hB : HasDerivedCategory B]
    [hC : HasDerivedCategory C] [hD : HasDerivedCategory D]
    [hBS : HasDerivedCategory (ℕᵒᵖ ⥤ B)] [hDS : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ D]
    (U : A ⥤ B) (P : B ⥤ D) (H : A ⥤ C) (U' : C ⥤ D)
    [U.Additive] [P.Additive] [H.Additive] [U'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj P)]
    [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj P)]
    (s : U ⋙ P ≅ H ⋙ U') (L : DiagonalRlim B) (L' : DiagonalRlim D)
    (β : L.R ⋙ P.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ B D).obj P).mapDerivedCategory ⋙ L'.R)
    {M : A} {M' : C} {S : ℕᵒᵖ ⥤ B} {S' : ℕᵒᵖ ⥤ D}
    (v : H.obj M ⟶ M')
    (b : ((Functor.whiskeringRight ℕᵒᵖ B D).obj P).obj S ⟶ S')
    (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ S)
    (π' : (Functor.const ℕᵒᵖ).obj (U'.obj M') ⟶ S')
    (K : DerivedCategory (ℕᵒᵖ ⥤ B)) (K' : DerivedCategory (ℕᵒᵖ ⥤ D))
    (a : K ≅ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj S)
    (a' : K' ≅ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0).obj S')
    (m : ((Functor.whiskeringRight ℕᵒᵖ B D).obj P).mapDerivedCategory.obj K ⟶ K')
    (hπ : (P.mapCone (Cone.mk _ π)).π ≫ b =
      (Functor.const ℕᵒᵖ).map (s.hom.app M ≫ U'.map v) ≫ π')
    (ha : ((Functor.whiskeringRight ℕᵒᵖ B D).obj P).mapDerivedCategory.map a.hom ≫
        (((Functor.whiskeringRight ℕᵒᵖ B D).obj P).mapDerivedCategorySingleFunctor 0).hom.app S ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0).map b = m ≫ a'.hom)
    (hβ : P.mapDerivedCategory.map (diagonalTraceConeMap L S (Cone.mk _ π)) ≫
        β.app ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj S) ≫
        L'.R.map ((((Functor.whiskeringRight ℕᵒᵖ B D).obj P).mapDerivedCategorySingleFunctor
          0).hom.app S) =
      (P.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
        diagonalTraceConeMap L' _ (P.mapCone (Cone.mk _ π))) :
    P.mapDerivedCategory.map
        ((U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
          diagonalTraceConeMap L S (Cone.mk _ π) ≫ L.R.map a.inv) ≫
        β.app K ≫ L'.R.map m =
      (Functor.mapDerivedCategorySquareIso s).hom.app
          ((DerivedCategory.singleFunctor A 0).obj M) ≫
        U'.mapDerivedCategory.map
          (diagonalSingleEndpointMap (hA := hA) (hB := hC) H v) ≫
        (U'.mapDerivedCategorySingleFunctor 0).hom.app M' ≫
        diagonalTraceConeMap L' S' (Cone.mk _ π') ≫ L'.R.map a'.inv := by
  unfold diagonalSingleEndpointMap
  let W := (Functor.whiskeringRight ℕᵒᵖ B D).obj P
  have hcancel : W.mapDerivedCategory.map a.inv ≫ m =
      (W.mapDerivedCategorySingleFunctor 0).hom.app S ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0).map b ≫ a'.inv := by
    apply (cancel_epi (W.mapDerivedCategory.map a.hom)).mp
    simp only [← W.mapDerivedCategory.map_comp_assoc, a.hom_inv_id,
      W.mapDerivedCategory.map_id, Category.id_comp]
    simpa only [Category.assoc, a'.hom_inv_id, Category.comp_id] using
      (congrArg (fun t ↦ t ≫ a'.inv) ha).symm
  have hnat := β.naturality a.inv
  dsimp only [Functor.comp_map] at hnat
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, ← L'.R.map_comp, hcancel]
  simp only [Functor.map_comp]
  rw [reassoc_of% hβ]
  have hc := traceCone_naturality L' (P.mapCone (Cone.mk _ π)) (Cone.mk _ π')
    (s.hom.app M ≫ U'.map v) b hπ
  rw [← reassoc_of% hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (exactSquare_single U P H U' s M)]
  have hv := (U'.mapDerivedCategorySingleFunctor 0).hom.naturality v
  dsimp only [Functor.comp_map] at hv
  rw [reassoc_of% hv]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
