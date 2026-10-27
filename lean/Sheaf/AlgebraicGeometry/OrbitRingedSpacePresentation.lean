module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Constructions

/-!
# Presentations of the invariant-section orbit ringed space

Source: ILO, Travaux de Gabber, IX 1.4, pp. 132--133 (quotient context), and
Stacks, Tags 0091, 0093 and 08ZK (explicit ringed-space and quotient definitions).
(blueprint: def-sfb-orbit-ringed-space-presentation)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- A presentation of the orbit topology and the invariant-section sheaf for an action
on a locally ringed space. The homeomorphism identifies the points with actual orbits;
the injective section maps identify the structure sheaf with the fixed subrings.
Naturality of `projection.hom.c` supplies the inherited restrictions. In `section_image`,
the open set pulled back from the orbit space is stable by `invariant`, so heterogeneous
equality is precisely equality after the canonical identification of that open with
its inverse image under the automorphism. No object is chosen from an existence proof.

Source: ILO IX 1.4, pp. 132--133, and Stacks Tags 0091, 0093, 08ZK.
(blueprint: def-sfb-orbit-ringed-space-presentation) -/
structure OrbitRingedSpacePresentation (G : Type v) [Group G]
    (X : LocallyRingedSpace.{u}) (action : G →* Aut X) where
  /-- The orbit space with its invariant-section sheaf of commutative rings. -/
  space : RingedSpace.{u, u}
  /-- Pullback is the inclusion of invariant sections. -/
  projection : X.toRingedSpace ⟶ space
  /-- The orbit quotient has the quotient topology. -/
  orbitHomeomorph : space.carrier ≃ₜ
    Quot (fun x y : X => ∃ g : G, (action g).hom.base x = y)
  /-- The projection sends a point to its orbit. -/
  projection_eq : ∀ x : X, orbitHomeomorph (projection.hom.base x) = Quot.mk _ x
  /-- Invariance includes the maps on sections, not just the maps on points. -/
  invariant : ∀ g : G, (action g).hom.toShHom ≫ projection = projection
  /-- Each section map is the inclusion of a subring. -/
  section_injective : ∀ T : Opens space,
    Function.Injective (projection.hom.c.app (op T))
  /-- Its image consists of exactly the sections fixed by every group element. -/
  section_image : ∀ (T : Opens space)
    (s : X.presheaf.obj (op ((Opens.map projection.hom.base).obj T))),
    (∃ t : space.presheaf.obj (op T), projection.hom.c.app (op T) t = s) ↔
      ∀ g : G, HEq
        ((action g).hom.c.app (op ((Opens.map projection.hom.base).obj T)) s) s

end AlgebraicGeometry
