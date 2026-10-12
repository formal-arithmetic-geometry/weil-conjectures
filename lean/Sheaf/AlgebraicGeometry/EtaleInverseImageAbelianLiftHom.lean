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
(blueprint: lem-weil-pbc-etale-inverse-image-abelian-lift-hom)

Proof: Use `sheaves_algebraicStructures_objects` to identify abelian sheaves
with internal commutative group objects on both sites, with their sectionwise
operations. Finite-limit preservation of L implies finite-product preservation.
Apply `Adjunction.liftsGroupRingObjects` to the set adjunction a. Transport the
resulting group-object adjunction through those identifications. Its right adjoint
is the abelian direct image: on each base-changed object it has the original
sections, operations and restrictions, so its underlying comparison with the set
direct image is the identity. The lift's hom-set equation therefore compares the
forgotten abelian adjunct with the set adjunct of its underlying comparison.

The transported left adjoint and `Etale.upperStar` are both left adjoint to this
same abelian direct image. Choose their comparison by `Adjunction.leftAdjointUniq`,
which intertwines the two adjunction bijections. Forget that comparison and compose
it with the lift's underlying isomorphism to obtain ea. Substitution in the lifted
hom-set equation gives exactly the displayed equation for every G, F and h. -/
theorem etaleInverseImageAbelianLift_hom (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∃ (ea : La ⋙ FaU ≅ FaV ⋙ L),
        (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
          FaV.map ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
            G F h) =
              a.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) := by sorry

end AlgebraicGeometry
