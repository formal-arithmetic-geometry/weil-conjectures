module
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Source: Stacks Project, Sites and Sheaves, Proposition 00YV.
(blueprint: lem-weil-pbc-etale-inverse-image-abelian-lift-ops)

Proof: Identify abelian sheaves with internal commutative group objects on each
site, with the sectionwise operation formulas of
`sheaves_algebraicStructures_objects`. Lift the set adjunction by
`Adjunction.liftsGroupRingObjects`; finite-limit preservation supplies its
finite-product hypothesis. Transport this lift back to abelian sheaves. Its right
adjoint is the sectionwise abelian direct image, because precomposition preserves
all the sectionwise operations and restriction maps. Uniqueness of left adjoints
therefore gives an abelian comparison from La to this lifted left adjoint. After
forgetting and composing with the lift's underlying comparison, call the resulting
isomorphism e0. The lifted hom-set equation and the adjunction-compatible abelian
comparison give the stated hom-set equation for e0.

The assumed hom-set equation forces ea = e0: for each G take F to be the lifted
left image of G and h to be the abelian comparison isomorphism. The hom-set
equations for ea and e0 have the same left side. Injectivity of the set adjunction
bijection and cancellation of the forgotten isomorphism h identify their inverse
components. Thus ea is the operation-compatible comparison e0.

Choose addV, zeroV, negV and addU, zeroU, negU from the internal-group
identifications. Their section formulas are exactly those in the conclusion.
The lifted addition equation, composed with the product comparison and transported
by the abelian comparison, gives the displayed addition equation; naturality of
the product comparison identifies its two factors with ea.inv. The lifted zero
equation gives the zero equation, since any map to the chosen terminal object is
terminal.from. The lifted inverse equation gives the negation equation after
cancelling ea. These transports are valid because the abelian comparison is a
group morphism. Substitute ea = e0 to conclude. -/
theorem etaleInverseImageAbelianLift_operations (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∀ (ea : La ⋙ FaU ≅ FaV ⋙ L),
        (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
          FaV.map ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
            G F h) =
              a.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) →
        (∀ G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1},
          ∃ (addV : (FaV.obj G) ⨯ (FaV.obj G) ⟶ (FaV.obj G))
            (addU : (FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G)) ⟶ (FaU.obj (La.obj G)))
            (zeroV : ⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1))) ⟶ (FaV.obj G))
            (zeroU : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶ (FaU.obj (La.obj G)))
            (negV : (FaV.obj G) ⟶ (FaV.obj G))
            (negU : (FaU.obj (La.obj G)) ⟶ (FaU.obj (La.obj G))),
            (∀ (W : V.Etaleᵒᵖ) (x : ((FaV.obj G) ⨯ (FaV.obj G)).obj.obj W),
              addV.hom.app W x =
                (@Add.add (G.obj.obj W) inferInstance
                  ((prod.fst : (FaV.obj G) ⨯ (FaV.obj G) ⟶
                      (FaV.obj G)).hom.app W x : G.obj.obj W)
                  ((prod.snd :
                    (FaV.obj G) ⨯ (FaV.obj G) ⟶ (FaV.obj G)).hom.app W x :
                    G.obj.obj W))) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : ((FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G))).obj.obj W),
              addU.hom.app W x =
                (@Add.add ((La.obj G).obj.obj W) inferInstance
                  ((prod.fst :
                    (FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G)) ⟶
                      (FaU.obj (La.obj G))).hom.app W x :
                    (La.obj G).obj.obj W)
                  ((prod.snd :
                    (FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G)) ⟶
                      (FaU.obj (La.obj G))).hom.app W x :
                    (La.obj G).obj.obj W))) ∧
            L.map addV = prodComparison L (FaV.obj G) (FaV.obj G) ≫
              prod.map (ea.inv.app G) (ea.inv.app G) ≫ addU ≫ ea.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              zeroV.hom.app W x = (0 : G.obj.obj W)) ∧
            (∀ (W : U.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              zeroU.hom.app W x = (0 : (La.obj G).obj.obj W)) ∧
            L.map zeroV = terminal.from _ ≫ zeroU ≫ ea.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ) (x : (FaV.obj G).obj.obj W),
              negV.hom.app W x = @Neg.neg (G.obj.obj W) inferInstance x) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : (FaU.obj (La.obj G)).obj.obj W),
              negU.hom.app W x = @Neg.neg ((La.obj G).obj.obj W) inferInstance x) ∧
            L.map negV = ea.inv.app G ≫ negU ≫ ea.hom.app G) := by sorry


end AlgebraicGeometry
