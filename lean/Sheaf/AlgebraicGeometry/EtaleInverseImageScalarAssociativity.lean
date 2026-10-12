/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Associativity and unit of the transported scalar action

Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-scalar-associativity). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-scalar-associativity).

Proof: Obtain the canonical ring and abelian lifts and the multiplication
and one transport equations from `etaleInverseImageAlgebraicStructures`.
As in the additive case, uniqueness of the lifted left adjoints and the two
assumed hom-equivalence equations identify the supplied er and ea with the
canonical comparisons after the lifted adjoint isomorphisms. Consequently the
multiplication and one of Lr(O) are the transported multiplication and one of O.

The source associativity diagram on (O times O) times G equates multiplication
of the two scalar factors followed by muV with the iterated action of the second
scalar and then the first. The source unit diagram on G inserts the constant
one in the first factor and applies muV; it equals the identity. Check both
diagrams on sections by the assumed formula for muV and the source module's
`mul_smul` and `one_smul` axioms. Apply L to these equalities. Rewrite the
triple-product comparison by its projections and naturality, and substitute
the multiplication transport formula; cancelling er and ea gives the
associativity diagram for mu. For the unit diagram use preservation of the
terminal object and its unique map, together with the one transport formula.
Evaluate the resulting diagrams at ((r,s),x) and at x. Sectionwise products
identify these evaluations with the two displayed equalities. This proves
associativity and the unit without assuming or asserting distributivity. -/
theorem etaleInverseImageScalarAssociativity (U V : Scheme.{u}) (f : U ⟶ V)
    (O : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    [PreservesFiniteLimits (Scheme.etaleSetPullback f)] :
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let a := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let aS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    ∀ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
        Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
    let OR := (sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj O)
    let OV := (sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
    let FV := SheafOfModules.toSheaf.{u + 1} OV
    ∀ (ea : La ⋙ FaU ≅ FaV ⋙ L),
      (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
        FrV.map (ar.homEquiv G F h) =
          aS.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
      (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
        FaV.map (a.homEquiv G F h) =
          aS.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) →
    ∀ G : SheafOfModules.{u + 1} OV,
    ∀ muV : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶ (FaV.obj (FV.obj G)),
      (∀ (W : V.Etaleᵒᵖ) (x : ((FrV.obj O) ⨯ (FaV.obj (FV.obj G))).obj.obj W),
        muV.hom.app W x =
          @SMul.smul (O.obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul
            ((prod.fst : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
              FrV.obj O).hom.app W x : O.obj.obj W)
            ((prod.snd : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
              FaV.obj (FV.obj G)).hom.app W x : G.val.obj W)) →
    let A := La.obj (FV.obj G)
    let mu := prod.map (er.hom.app O) (ea.hom.app (FV.obj G)) ≫
      inv (prodComparison L (FrV.obj O) (FaV.obj (FV.obj G))) ≫
      L.map muV ≫ ea.inv.app (FV.obj G)
    let e : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ≅
        (FrU.obj (Lr.obj O)) ⊗ (FaU.obj A) :=
      (limit.isLimit _).conePointUniqueUpToIso
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
    let act : ∀ W : U.Etaleᵒᵖ, OR.obj.obj W → A.obj.obj W → A.obj.obj W :=
      fun W r x ↦ (e.inv ≫ mu).hom.app W (r, x)
    ∀ W : U.Etaleᵒᵖ,
      (∀ (r s : OR.obj.obj W) (x : A.obj.obj W),
        act W (r * s) x = act W r (act W s x)) ∧
      (∀ x : A.obj.obj W, act W 1 x = x)
    := by sorry

end AlgebraicGeometry
