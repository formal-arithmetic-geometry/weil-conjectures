module

public import Sheaf.AlgebraicGeometry.OrbitRingedSpacePresentation
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Invariant-section orbit ringed spaces and factorization

Source: ILO, Travaux de Gabber, IX 1.4, pp. 132--133, and the explicit construction
from Stacks Tags 006T, 0072, 0091, 0093, 01HB, 00A1, 01IJ and 08ZK.
(blueprint: lem-sfb-orbit-invariant-ringed-space-factorization)

The declarations give existence of the invariant-section sheaf on the actual orbit
topology, openness, ringed-space factorization, locality, invariant-open comparison,
and the resulting scheme factorization. No representability theorem is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- The orbit topology carries the sheaf of invariant sections and its inclusion map.
No finiteness of the acting group is required.

Source: ILO IX 1.4, pp. 132--133; Stacks Tags 006T, 0072, 0091, 0093 and 08ZK.
(blueprint: lem-sfb-orbit-invariant-ringed-space-factorization)

Proof: The orbit relation gives the quotient topology. Each automorphism preserves
the inverse image of every quotient open. Its fixed sections form a subring and
restriction preserves them. Glue a matching family in the structure sheaf of X.
Pulling the glued section back by any group element gives another gluing of the
same family, hence the same section; this includes the empty cover. The inclusions
are natural ring maps and define the projection. Its invariance holds on points
and on sections. These are Steps 1--3 of the node, using
[def-weil-locally-ringed-space-morphism]. -/
theorem exists_orbitRingedSpacePresentation (G : Type v) [Group G]
    (X : LocallyRingedSpace.{u}) (action : G →* Aut X) :
    Nonempty (OrbitRingedSpacePresentation G X action) := by
  sorry

/-- The projection to the orbit ringed space is open.

Source: Stacks Tag 08ZK and ILO IX 1.4, pp. 132--133.
(blueprint: lem-sfb-orbit-invariant-ringed-space-factorization)

Proof: Step 1 computes the inverse image of the image of an open U as the union
of its translates. Each translate is open because the action is by automorphisms
[def-weil-locally-ringed-space-morphism]. The quotient topology then makes the
image open. -/
theorem OrbitRingedSpacePresentation.isOpenMap (G : Type v) [Group G]
    (X : LocallyRingedSpace.{u}) (action : G →* Aut X)
    (D : OrbitRingedSpacePresentation G X action) :
    IsOpenMap D.projection.hom.base := by
  sorry

/-- Every invariant ringed-space morphism factors uniquely through the projection.
The target need not be locally ringed.

Source: Stacks Tags 0091, 0093 and 08ZK; ILO IX 1.4, pp. 132--133.
(blueprint: lem-sfb-orbit-invariant-ringed-space-factorization)

Proof: Steps 4--6 descend the point map, constant on each orbit, by the quotient
topology. Invariance of the morphism on sections makes its pullbacks invariant,
so the section maps land in exactly the image specified by section_image.
Their ring laws and naturality are inherited from the given map. This constructs
the factor. Surjectivity on points and injectivity on invariant sections prove
uniqueness, by [def-weil-locally-ringed-space-morphism]. -/
theorem OrbitRingedSpacePresentation.existsUnique_factor (G : Type v) [Group G]
    (X : LocallyRingedSpace.{u}) (action : G →* Aut X)
    (D : OrbitRingedSpacePresentation G X action)
    (Z : RingedSpace.{u, u}) (a : X.toRingedSpace ⟶ Z)
    (ha : ∀ g : G, (action g).hom.toShHom ≫ a = a) :
    ∃! b : D.space ⟶ Z, D.projection ≫ b = a := by
  sorry

/-- Under the stated local-stalk hypotheses the unique ringed-space factor is local.
Together with the local rings on D.space this is a locally ringed space morphism.

Source: Stacks Tag 01HB; ILO IX 1.4, pp. 132--133.
(blueprint: lem-sfb-orbit-invariant-ringed-space-factorization)

Proof: Step 7 chooses a point x over each orbit y. On germs, functoriality identifies
the composite of the factor stalk map and the projection stalk map with the stalk
map of a. The latter and the projection are local. The inverse image of the maximal
ideal along the projection is the maximal ideal of the quotient stalk. It follows
that the factor carries the maximal ideal into the maximal ideal. Apply the ringed
factorization of Steps 4--6 for existence and uniqueness, and
[def-weil-locally-ringed-space-morphism] to recognize the local morphism. -/
theorem OrbitRingedSpacePresentation.existsUnique_local_factor (G : Type v) [Group G]
    (X : LocallyRingedSpace.{u}) (action : G →* Aut X)
    (D : OrbitRingedSpacePresentation G X action)
    (hY : ∀ y : D.space, IsLocalRing (D.space.presheaf.stalk y))
    (hq : ∀ x : X, IsLocalHom (D.projection.hom.stalkMap x).hom)
    (Z : LocallyRingedSpace.{u}) (a : X ⟶ Z)
    (ha : ∀ g : G, (action g).hom ≫ a = a) :
    ∃! b : D.space ⟶ Z.toRingedSpace,
      D.projection ≫ b = a.toShHom ∧
        ∀ y : D.space, IsLocalHom (b.hom.stalkMap y).hom := by
  sorry

/-- On an invariant open, the orbit construction is canonically the open restriction.
The restricted action and projection are specified by their inclusion squares. The
preceding factorization theorems therefore apply to this same restricted quotient.
The local-stalk hypotheses pass to it.

Source: Stacks Tags 00A1, 0078 and 08ZK; ILO IX 1.4, pp. 132--133.
(blueprint: lem-sfb-orbit-invariant-ringed-space-factorization)

Proof: Step 8 uses Step 1 to see that O = q(W) is open and has inverse image W.
The restricted automorphisms give the action on W. The bijection W/G to O is a
homeomorphism because W is open and both spaces have the quotient topology.
On every open of O the invariant sections for W are exactly those for X, and
the restrictions and inclusion maps agree. Thus this comparison is an isomorphism
of ringed spaces with the stated square. Intersecting neighborhoods with W and O
identifies stalks and projection stalk maps, so localness passes to the restriction.
Steps 2--7 apply to the restricted action as well, using
[def-weil-locally-ringed-space-morphism]. -/
theorem OrbitRingedSpacePresentation.invariant_open (G : Type v) [Group G]
    (X : LocallyRingedSpace.{u}) (action : G →* Aut X)
    (D : OrbitRingedSpacePresentation G X action) (W : Opens X)
    (hW : ∀ g : G, (Opens.map (action g).hom.base).obj W = W) :
    ∃ (O : Opens D.space)
      (actionW : G →* Aut (X.restrict W.isOpenEmbedding))
      (DW : OrbitRingedSpacePresentation G (X.restrict W.isOpenEmbedding) actionW)
      (comparison : DW.space ≅ D.space.restrict O.isOpenEmbedding),
      (O : Set D.space) = D.projection.hom.base '' (W : Set X) ∧
      D.projection.hom.base ⁻¹' (O : Set D.space) = (W : Set X) ∧
      (∀ g : G, (actionW g).hom ≫ X.ofRestrict W.isOpenEmbedding =
        X.ofRestrict W.isOpenEmbedding ≫ (action g).hom) ∧
      DW.projection ≫ comparison.hom ≫ D.space.ofRestrict O.isOpenEmbedding =
        (X.ofRestrict W.isOpenEmbedding).toShHom ≫ D.projection ∧
      ((∀ y : D.space, IsLocalRing (D.space.presheaf.stalk y)) →
        (∀ x : X, IsLocalHom (D.projection.hom.stalkMap x).hom) →
        (∀ y : DW.space, IsLocalRing (DW.space.presheaf.stalk y)) ∧
          ∀ x : X.restrict W.isOpenEmbedding,
            IsLocalHom (DW.projection.hom.stalkMap x).hom) := by
  sorry

/-- If both ringed spaces are schemes, the projection and factorizations are scheme
morphisms. The ringed-space isomorphisms express scheme structures on the same
objects without assuming that any orbit ringed space is representable.
Applied to the presentation in invariant_open, this also gives the scheme
factorizations on every invariant open.

Source: Stacks Tags 01HB, 01IJ, 0078 and 08ZK; ILO IX 1.4, pp. 132--133.
(blueprint: lem-sfb-orbit-invariant-ringed-space-factorization)

Proof: Step 9 uses [def-pc-scheme] to obtain local quotient stalks. If an invariant
section becomes invertible at x, invert it near x. Translate that neighborhood
and its inverse by every g and glue the inverses, which agree by uniqueness, on
the saturated open. The glued inverse is invariant and descends to the quotient.
Thus the projection stalk maps reflect units, so are local. The factor is local
by Step 7, hence a scheme morphism by [def-weil-locally-ringed-space-morphism]
and [def-pc-scheme]. Ringed-space uniqueness proves scheme uniqueness. Step 8
identifies the restricted quotient; open restrictions of the schemes give the
same argument there. No affine-chart or scheme representability is constructed. -/
theorem OrbitRingedSpacePresentation.existsUnique_scheme_factor (G : Type v) [Group G]
    (X : LocallyRingedSpace.{u}) (action : G →* Aut X)
    (D : OrbitRingedSpacePresentation G X action)
    (SX SY : Scheme.{u}) (eX : SX.toRingedSpace ≅ X.toRingedSpace)
    (eY : SY.toRingedSpace ≅ D.space) :
    ∃ q : SX ⟶ SY,
      q.toLRSHom.toShHom = eX.hom ≫ D.projection ≫ eY.inv ∧
      ∀ (Z : Scheme.{u}) (a : SX ⟶ Z),
        (∀ g : G, (action g).hom.toShHom ≫ eX.inv ≫ a.toLRSHom.toShHom =
          eX.inv ≫ a.toLRSHom.toShHom) →
        ∃! b : SY ⟶ Z, q ≫ b = a := by
  sorry

end AlgebraicGeometry
