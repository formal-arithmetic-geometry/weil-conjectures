module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Coherent systems with specified tensor restrictions on a tower of spaces

Source: Stacks Project, spaces-more-morphisms.tex, Tag 08BF, conditions (1) and (2)
(blueprint: def-sfb-space-thickening-coherent-systems).

The arbitrary tower is indexed starting at zero. Morphisms are all compatible
component maps, with componentwise identities and composition. This is the
algebraic-space small-etale counterpart of the scheme category of Tag 088F.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Coherence means site quasi-coherence and coherence on every etale scheme chart.
Source: Stacks, Tags 07UB and 08AM
(blueprint: def-sfb-space-thickening-coherent-systems). -/
abbrev ClosedAdicCoherent (X : AlgebraicSpace S) : ObjectProperty X.Modules :=
  fun M ↦ M.IsQuasicoherent ∧ ∀ T : X.EtaleSite,
    RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
      ((X.schemeRestriction T).obj M)

/-- Coherent modules on the successive thickenings, retaining the specified adjacent
isomorphisms, rather than merely asserting that those isomorphisms exist.
Source: Stacks, Tag 08BF, conditions (1) and (2)
(blueprint: def-sfb-space-thickening-coherent-systems). -/
structure ClosedAdicRestrictionSystem (Y : ℕ → AlgebraicSpace S)
    (j : ∀ n : ℕ, Y n ⟶ Y (n + 1)) where
  term (n : ℕ) : (Y n).Modules
  coherent (n : ℕ) : ClosedAdicCoherent (Y n) (term n)
  restriction (n : ℕ) : (moduleTensorPullback (j n)).obj (term (n + 1)) ≅ term n

namespace ClosedAdicRestrictionSystem

variable {Y : ℕ → AlgebraicSpace S} {j : ∀ n : ℕ, Y n ⟶ Y (n + 1)}

/-- Arrows are all component maps commuting with the specified tensor restrictions.
Source: Stacks, Tag 08BF, systems and their morphisms
(blueprint: def-sfb-space-thickening-coherent-systems). -/
structure Hom (F G : ClosedAdicRestrictionSystem Y j) where
  app (n : ℕ) : F.term n ⟶ G.term n
  comm (n : ℕ) : (moduleTensorPullback (j n)).map (app (n + 1)) ≫
    (G.restriction n).hom = (F.restriction n).hom ≫ app n

/-- Component identities satisfy the restriction square.
Source: Stacks, Tag 08BF (blueprint: def-sfb-space-thickening-coherent-systems).
Proof: functors preserve identity maps, and both sides reduce by the category unit laws. -/
theorem identity_comm (F : ClosedAdicRestrictionSystem Y j) (n : ℕ) :
    (moduleTensorPullback (j n)).map (𝟙 (F.term (n + 1))) ≫ (F.restriction n).hom =
      (F.restriction n).hom ≫ 𝟙 (F.term n) := by
  sorry

/-- The identity has the component identity maps.
Source: Stacks, Tag 08BF (blueprint: def-sfb-space-thickening-coherent-systems). -/
def identity (F : ClosedAdicRestrictionSystem Y j) : Hom F F :=
  ⟨fun n ↦ 𝟙 (F.term n), identity_comm F⟩

/-- Component composition satisfies the restriction square.
Source: Stacks, Tag 08BF (blueprint: def-sfb-space-thickening-coherent-systems).
Proof: expand functoriality of the tensor pullback, apply the second arrow's square,
then the first arrow's square, and reassociate. -/
theorem composition_comm {F G H : ClosedAdicRestrictionSystem Y j}
    (f : Hom F G) (g : Hom G H) (n : ℕ) :
    (moduleTensorPullback (j n)).map (f.app (n + 1) ≫ g.app (n + 1)) ≫
        (H.restriction n).hom = (F.restriction n).hom ≫ (f.app n ≫ g.app n) := by
  sorry

/-- Composition has the component composite maps.
Source: Stacks, Tag 08BF (blueprint: def-sfb-space-thickening-coherent-systems). -/
def composition {F G H : ClosedAdicRestrictionSystem Y j} (f : Hom F G) (g : Hom G H) :
    Hom F H :=
  ⟨fun n ↦ f.app n ≫ g.app n, composition_comm f g⟩

/-- Componentwise category laws.
Source: Stacks, Tag 08BF (blueprint: def-sfb-space-thickening-coherent-systems).
Proof: equality of arrows is equality of their component maps, since commutativity
is a proposition. The three equations are therefore the category laws at each level. -/
theorem category_laws :
    (∀ {F G : ClosedAdicRestrictionSystem Y j} (f : Hom F G),
      composition (identity F) f = f) ∧
    (∀ {F G : ClosedAdicRestrictionSystem Y j} (f : Hom F G),
      composition f (identity G) = f) ∧
    (∀ {F G H K : ClosedAdicRestrictionSystem Y j} (f : Hom F G) (g : Hom G H)
      (h : Hom H K), composition (composition f g) h = composition f (composition g h)) := by
  sorry

/-- The category with the displayed objects, arrows, identities and compositions.
Source: Stacks, Tag 08BF (blueprint: def-sfb-space-thickening-coherent-systems). -/
instance instCategory : Category (ClosedAdicRestrictionSystem Y j) where
  Hom := Hom
  id := identity
  comp := composition
  id_comp := category_laws.1
  comp_id := category_laws.2.1
  assoc := category_laws.2.2

/-- Evaluation retains the actual component module and component map.
Source: Stacks, Tag 08BF (blueprint: def-sfb-space-thickening-coherent-systems). -/
def evaluation (n : ℕ) : ClosedAdicRestrictionSystem Y j ⥤ (Y n).Modules where
  obj F := F.term n
  map f := f.app n

end ClosedAdicRestrictionSystem

end AlgebraicGeometry.AlgebraicSpace
