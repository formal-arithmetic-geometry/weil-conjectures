/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# EtaleInverseImageRingLift

Source: Stacks Project, Sites and Sheaves, Proposition 00YV.
(blueprint: lem-weil-pbc-etale-inverse-image-ring-lift).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Source: Stacks Project, Sites and Sheaves, Proposition 00YV and its preceding
quadruple/sextuple descriptions.
(blueprint: lem-weil-pbc-etale-inverse-image-ring-lift).

Proof: Identify ring-valued sheaves on both sites with internal commutative ring
objects using `sheaves_algebraicStructures_objects`. Apply the ring clause of
`Adjunction.liftsGroupRingObjects` to the set adjunction and `hL`. Transport its
left functor through the inverse ring-object/sheaf functors to obtain `Lr`.
The right functor so obtained is canonically the sectionwise direct image `Rr`:
evaluation at each base-changed object preserves all five ring operations and all
restriction homomorphisms. Use this identification to transport the lifted adjunction
and call it `ar`. The underlying left comparison gives `er`; restricting the set
adjunction bijection gives the displayed hom-set equation. Choose addition, zero,
negation, multiplication and one to be the sectionwise operations under the
ring-object/sheaf identification. The five lift formulas, expressed through `er`,
give their transport equations below. For the binary operations compose the inverse
product comparison with the two inverse components of `er`, and then cancel the
comparison; for the constants use the unique map to the terminal object; for negation
use the inverse component directly. Their section formulas are precisely those of
the identification of ring sheaves with ring objects. The unit equation is not
assumed here and will be deduced from the hom-set equation in the parent theorem. -/
theorem etaleInverseImageRingLift (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
          Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
        (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
          FrV.map (ar.homEquiv G F h) =
            a.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
        (∀ G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1},
          ∃ (addV : (FrV.obj G) ⨯ (FrV.obj G) ⟶ (FrV.obj G))
            (addU : (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶ (FrU.obj (Lr.obj G)))
            (zeroV : ⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1))) ⟶ (FrV.obj G))
            (zeroU : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶ (FrU.obj (Lr.obj G)))
            (negV : (FrV.obj G) ⟶ (FrV.obj G))
            (negU : (FrU.obj (Lr.obj G)) ⟶ (FrU.obj (Lr.obj G)))
            (mulV : (FrV.obj G) ⨯ (FrV.obj G) ⟶ (FrV.obj G))
            (mulU : (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶ (FrU.obj (Lr.obj G)))
            (oneV : ⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1))) ⟶ (FrV.obj G))
            (oneU : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶ (FrU.obj (Lr.obj G))),
            (∀ (W : V.Etaleᵒᵖ) (x : ((FrV.obj G) ⨯ (FrV.obj G)).obj.obj W),
              addV.hom.app W x =
                (@Add.add (G.obj.obj W) inferInstance
                  ((prod.fst : (FrV.obj G) ⨯ (FrV.obj G) ⟶
                      (FrV.obj G)).hom.app W x : G.obj.obj W)
                  ((prod.snd :
                    (FrV.obj G) ⨯ (FrV.obj G) ⟶ (FrV.obj G)).hom.app W x :
                    G.obj.obj W))) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : ((FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G))).obj.obj W),
              addU.hom.app W x =
                (@Add.add ((Lr.obj G).obj.obj W) inferInstance
                  ((prod.fst :
                    (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶
                      (FrU.obj (Lr.obj G))).hom.app W x :
                    (Lr.obj G).obj.obj W)
                  ((prod.snd :
                    (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶
                      (FrU.obj (Lr.obj G))).hom.app W x :
                    (Lr.obj G).obj.obj W))) ∧
            L.map addV = prodComparison L (FrV.obj G) (FrV.obj G) ≫
              prod.map (er.inv.app G) (er.inv.app G) ≫ addU ≫ er.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              zeroV.hom.app W x = (0 : G.obj.obj W)) ∧
            (∀ (W : U.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              zeroU.hom.app W x = (0 : (Lr.obj G).obj.obj W)) ∧
            L.map zeroV = terminal.from _ ≫ zeroU ≫ er.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ) (x : (FrV.obj G).obj.obj W),
              negV.hom.app W x = @Neg.neg (G.obj.obj W) inferInstance x) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : (FrU.obj (Lr.obj G)).obj.obj W),
              negU.hom.app W x = @Neg.neg ((Lr.obj G).obj.obj W) inferInstance x) ∧
            L.map negV = er.inv.app G ≫ negU ≫ er.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ) (x : ((FrV.obj G) ⨯ (FrV.obj G)).obj.obj W),
              mulV.hom.app W x =
                (@Mul.mul (G.obj.obj W) inferInstance
                  ((prod.fst : (FrV.obj G) ⨯ (FrV.obj G) ⟶
                      (FrV.obj G)).hom.app W x : G.obj.obj W)
                  ((prod.snd :
                    (FrV.obj G) ⨯ (FrV.obj G) ⟶ (FrV.obj G)).hom.app W x :
                    G.obj.obj W))) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : ((FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G))).obj.obj W),
              mulU.hom.app W x =
                (@Mul.mul ((Lr.obj G).obj.obj W) inferInstance
                  ((prod.fst :
                    (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶
                      (FrU.obj (Lr.obj G))).hom.app W x :
                    (Lr.obj G).obj.obj W)
                  ((prod.snd :
                    (FrU.obj (Lr.obj G)) ⨯ (FrU.obj (Lr.obj G)) ⟶
                      (FrU.obj (Lr.obj G))).hom.app W x :
                    (Lr.obj G).obj.obj W))) ∧
            L.map mulV = prodComparison L (FrV.obj G) (FrV.obj G) ≫
              prod.map (er.inv.app G) (er.inv.app G) ≫ mulU ≫ er.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              oneV.hom.app W x = (1 : G.obj.obj W)) ∧
            (∀ (W : U.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              oneU.hom.app W x = (1 : (Lr.obj G).obj.obj W)) ∧
            L.map oneV = terminal.from _ ≫ oneU ≫ er.hom.app G) := by sorry

end AlgebraicGeometry
