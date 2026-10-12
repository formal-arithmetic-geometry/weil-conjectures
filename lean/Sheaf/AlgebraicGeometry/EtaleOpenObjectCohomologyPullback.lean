module

public import Sheaf.AlgebraicGeometry.EtaleOpenFreeSheafPullback
import Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The open-object map commutes with pullback of arbitrary Ext classes.
Source: Stacks Project, Tag 03F3 (localization), and functoriality, Tags 01F8/01FB.
(blueprint: lem-weil-pbc-etale-open-object-cohomology-pullback)

Proof: Expand etaleOpenObjectCohomologyMap as exact inverse image for the open
inclusion followed by precomposition with its identity generator. Expand
openCohomologyPullback as inverse image along morphismRestrict followed by
its two inverse-image composition identifications. Move precomposition through
exact inverse image using Ext.mapExactFunctor_comp and mapExactFunctor_mk₀.
The square (morphismRestrict g W) ≫ W.ι = (g⁻¹W).ι ≫ g identifies the two
composed inverse-image functors. Apply exactFunctorCompositionComparison to x
for both sides of this square. The remaining degree-zero morphism equality
says that the identity generator on g⁻¹W, followed by the inverse image of
etaleOpenFreeSheafPullback, is the pullback of the identity generator on W,
transported by the constant-sheaf and inverse-image composition isomorphisms.
To verify this equality, use the constant-sheaf sections adjunction, then
expand etaleOpenFreeSheafPullback and etaleOpenFreeSheafSection: both send 1
to the sheafification of the identity generator restricted along
openSectionPullback. Naturality of the unit and of the localization restriction
isomorphism gives the coefficient transport. Ext associativity finishes.
This statement has no resolutions, chain maps, or chosen cocycles. -/
theorem etaleOpenObjectCohomologyMap_pullback
    {X Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Opens)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Abelian.Ext ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι)) G q) :
    etaleOpenObjectCohomologyMap ((upperStar AddCommGrpCat.{u + 1} g).obj G)
      q (g ⁻¹ᵁ W)
        ((Abelian.Ext.mk₀ (etaleOpenFreeSheafPullback g W)).comp
          (x.mapExactFunctor (upperStar AddCommGrpCat.{u + 1} g)) (zero_add q)) =
      openCohomologyPullback g W G q (etaleOpenObjectCohomologyMap G q W x) := by sorry

end AlgebraicGeometry.Etale
