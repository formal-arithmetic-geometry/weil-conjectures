/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Identifying the ring-object lift of sectionwise etale direct image

Source: Stacks Project, Proposition 00YV, ring paragraph and Section 00YR.
(blueprint: lem-weil-pbc-etale-ring-direct-image-operations).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
namespace AlgebraicGeometry

/-- Source: Stacks Project, Proposition 00YV, ring paragraph; Section 00YR, sextuples.
(blueprint: lem-weil-pbc-etale-ring-direct-image-operations).

Proof: Fix X and an etale object Z. For any internal ring Y on either site,
apply the supplied section formulas to GY. The equality G F = id identifies
F(GY) with Y as an internal ring, hence identifies all its operations.
The forgetful equalities make the composite of the resulting underlying
identifications the identity. Thus the inverse of eG carries the internal
addition, zero, multiplication and one to the corresponding section operations
of GY. For sectionwise direct image R, the inverse product comparison sends a
pair of sections to that same pair at the base-changed object: compose with the
two projections to check this assertion. The inverse terminal comparison sends
the unique singleton section to the unique singleton section. Evaluate each of
the supplied RF addition, zero, multiplication and one equations at Z, and apply
these product and terminal descriptions. Finally use the preceding operation
identifications for GU and GV. The four resulting equations are exactly the
four assertions for c. This calculation is valid for the zero ring and requires
no points or nonempty sections. It asserts only preservation of operations;
constructing ring homomorphisms, proving invertibility and proving naturality
are separate steps handled by the importing module. -/
theorem etaleRingDirectImageOperations (U V : Scheme.{u}) (f : U ⟶ V)
    (FU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1} ⥤
      CommRingObjCat (Sheaf U.smallEtaleTopology (Type (u + 1))))
    (GU : CommRingObjCat (Sheaf U.smallEtaleTopology (Type (u + 1))) ⥤
      Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
    (hFU : FU ⋙ CommRingObjCat.forget _ = sheafForget U.smallEtaleTopology)
    (hGU : GU ⋙ sheafForget U.smallEtaleTopology = CommRingObjCat.forget _)
    (hGUFU : GU ⋙ FU = 𝟭 _)
    (opsU : (∀ (A : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (Z : U.Etaleᵒᵖ),
        (∀ a b : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z
            ((AddMonObj.add (X := (FU.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a) +
              (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((AddMonObj.zero (X := (FU.obj A).X)).hom.app Z t) =
            (0 : A.obj.obj Z)) ∧
        (∀ a : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((AddGrpObj.neg (X := (FU.obj A).X)).hom.app Z a) =
            -(show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a)) ∧
        (∀ a b : (FU.obj A).X.obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((MonObj.mul (X := (FU.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z a) *
              (show A.obj.obj Z from ((eqToIso hFU).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj Z,
          ((eqToIso hFU).hom.app A).hom.app Z ((MonObj.one (X := (FU.obj A).X)).hom.app Z t) =
            (1 : A.obj.obj Z))))
    (FV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
      CommRingObjCat (Sheaf V.smallEtaleTopology (Type (u + 1))))
    (GV : CommRingObjCat (Sheaf V.smallEtaleTopology (Type (u + 1))) ⥤
      Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    (hFV : FV ⋙ CommRingObjCat.forget _ = sheafForget V.smallEtaleTopology)
    (hGV : GV ⋙ sheafForget V.smallEtaleTopology = CommRingObjCat.forget _)
    (hGVFV : GV ⋙ FV = 𝟭 _)
    (opsV : (∀ (A : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}) (Z : V.Etaleᵒᵖ),
        (∀ a b : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z
            ((AddMonObj.add (X := (FV.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a) +
              (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((AddMonObj.zero (X := (FV.obj A).X)).hom.app Z t) =
            (0 : A.obj.obj Z)) ∧
        (∀ a : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((AddGrpObj.neg (X := (FV.obj A).X)).hom.app Z a) =
            -(show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a)) ∧
        (∀ a b : (FV.obj A).X.obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((MonObj.mul (X := (FV.obj A).X)).hom.app Z (a, b)) =
            (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z a) *
              (show A.obj.obj Z from ((eqToIso hFV).hom.app A).hom.app Z b)) ∧
        (∀ t : (𝟙_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj Z,
          ((eqToIso hFV).hom.app A).hom.app Z ((MonObj.one (X := (FV.obj A).X)).hom.app Z t) =
            (1 : A.obj.obj Z)))) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let R := b.sheafPushforwardContinuous (Type (u + 1))
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    ∀ (RF : CommRingObjCat (Sheaf U.smallEtaleTopology (Type (u + 1))) ⥤
          CommRingObjCat (Sheaf V.smallEtaleTopology (Type (u + 1))))
      (hRF : RF ⋙ CommRingObjCat.forget _ = CommRingObjCat.forget _ ⋙ R)
      [PreservesFiniteProducts R],
      (∀ X : CommRingObjCat (Sheaf U.smallEtaleTopology (Type (u + 1))),
            AddMonObj.add (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              ((eqToIso hRF).hom.app X ⊗ₘ (eqToIso hRF).hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (AddMonObj.add (X := X.X)) ∧
            AddMonObj.zero (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (AddMonObj.zero (X := X.X)) ∧
            AddGrpObj.neg (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (eqToIso hRF).hom.app X ≫ R.map (AddGrpObj.neg (X := X.X)) ∧
            MonObj.mul (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              ((eqToIso hRF).hom.app X ⊗ₘ (eqToIso hRF).hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ (eqToIso hRF).hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X))) →
      ∀ X (Z : V.Etaleᵒᵖ),
        let c : (GV.obj (RF.obj X)).obj.obj Z → (Rr.obj (GU.obj X)).obj.obj Z :=
          ((eqToIso hGV).hom.app (RF.obj X) ≫
          (eqToIso hRF).hom.app X ≫ R.map ((eqToIso hGU).inv.app X)).hom.app Z
        (∀ a b : (GV.obj (RF.obj X)).obj.obj Z, c (a + b) = c a + c b) ∧
        c (0 : (GV.obj (RF.obj X)).obj.obj Z) = 0 ∧
        (∀ a b : (GV.obj (RF.obj X)).obj.obj Z, c (a * b) = c a * c b) ∧
        c (1 : (GV.obj (RF.obj X)).obj.obj Z) = 1 := by sorry

end AlgebraicGeometry
