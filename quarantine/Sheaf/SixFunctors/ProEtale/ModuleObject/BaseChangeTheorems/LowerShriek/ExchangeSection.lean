/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import all Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono

/-! Componentwise geometric inputs for cartesian extension by zero. -/

@[expose] public section

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

section
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
include ℓ k

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  (j : X ⟶ Z) (g : Z' ⟶ Z) (j' : X' ⟶ Z') (g' : X' ⟶ X)
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]

variable {j g j' g'}

/-- Source: blueprint `thm-sfb-dc-open-base-change-iso`, cartesian extension-by-zero
argument; compare `ProEtale.openImmersionLowerShriekBaseChangeIso` for abelian sheaves.

The equality parameter presents the canonical unit--square--counit composite without copying
its definition from the importing module. It is discharged there by reflexivity.

Proof: For abelian pro-etale sheaves, cartesian extension-by-zero base change identifies the
inverse image of the extension by zero with extension by zero from the pulled-back open.
The comparison is linear over the pulled-back coefficient ring: its map on the open is the
identity after the cartesian identification, and extension by zero gives the unique action
away from the open. The coefficient morphisms are isomorphisms, so scalar transport preserves
this identification. Under the canonical scalar-transport
isomorphisms, the adjunction units, counits and pullback composition comparisons on module
objects forget to these sheaf comparisons: expand the lifted adjunctions and cancel the
coefficient-isomorphism inverse pairs using their triangle identities. Their displayed mate
is therefore precisely the linear exchange map. All four functors are exact. Applying this
sheaf-level comparison and its inverse degreewise commutes with differentials and descends through
quasi-isomorphisms.
The compatibility isomorphisms defining the restricted bounded constructible functors and
adjunctions therefore identify the displayed composite on K with this derived exchange.
Take the component of the degreewise inverse under these compatibility isomorphisms.
It is a morphism from the target to the source whose composite with α.app K is the identity,
since the degreewise inverse equation survives localization and restriction. Only existence
for this fixed K is asserted; the theorem does not choose data or assert naturality in K.
(blueprint: stage3-sfb-open-base-change-component-section) -/
theorem boundedConstructibleOpenImmersionLowerShriekBaseChange_app_section
    (sq : IsPullback g' j' j g)
    (α : boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g)
    (hα : α =
      ((Functor.leftUnitor _).inv ≫ Functor.whiskerRight
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit
        (boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j')) ≫
      (Functor.squareTransport (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq.toCommSq.flip)).hom ≫
      (Functor.whiskerLeft
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
          boundedConstructibleUpperStar Λ ℓ g)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').counit ≫
        (Functor.rightUnitor _).hom))
    (K : Dᵇc(X.left)⟦Λ⟧) :
    ∃ β : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g).obj K ⟶
      (boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ j').obj K,
      β ≫ α.app K = 𝟙 _ := by
  have := sharedBoundedOpenUnitIsIso Λ ℓ j
  -- Cartesian support makes the counit invertible on the target of the exchange.
  have := boundedCartesianCounit Λ ℓ sq K
  have : IsIso (α.app K) := by
    rw [hα]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_obj]
    infer_instance
  exact ⟨inv (α.app K), IsIso.inv_hom_id _⟩

end
end AlgebraicGeometry.ProEtale.CondensedRing
