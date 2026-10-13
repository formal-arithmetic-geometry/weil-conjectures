/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion

/-! # Horizontal differential of explicit subset insertion

Source: Stacks Project, Tag 08C1 and equation (20.40.0.1) (Tag 08C0),
and Tag 01FG, ordered-complex differential preceding Definition 20.23.2.
(blueprint: lem-sc-principal-open-cech-subset-insertion-horizontal).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

/-- The horizontal total differential on explicit subset coordinates.

Source: Stacks Project, Tag 08C1, equation (20.40.0.1) (Tag 08C0), and
Tag 01FG, ordered-complex differential preceding Definition 20.23.2.
(blueprint: lem-sc-principal-open-cech-subset-insertion-horizontal).

Proof: Expand insertion as its finite sum, and apply Mathlib's `ι_D₁` and
`d₁_eq` to each summand. Its horizontal sign is one. Extension by zero identifies
the horizontal map with alternatingCechDifferential, whose target tuple coordinate
is the signed sum of restrictions from the tuples obtained by deleting one entry.
Increasing tuples are uniquely determined by their ranges. For the increasing
enumeration of a target subset S, deleting the position occupied by j gives the
increasing enumeration of S.erase j. That position is exactly the cardinality of
the elements of S smaller than j. Section transport commutes with restrictions:
compose the open equality maps and use functoriality of the presheaf, naturality
of restriction, and the natural isomorphism overFunctorEquiv. The resulting open
map is the one from hle, since opens form a thin category. Use he to identify the
coefficient degrees, and proof irrelevance to identify the equality transports.
Regroup the finite sums by target subsets, and reassemble the tuple coordinates
using the total inclusions. For singleton targets the erased set is empty: the
source column would be negative and is zero by extension. For an empty cover
all sums are zero. These cover the boundary cases without a coefficient bound. -/
theorem principalSubsetInsertion_horizontal
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) :
    let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let K := (alternatingCechDoubleFunctor U).obj (principalSubsetRestriction A r f J)
    let H := forget₂
      (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
    let D := principalSubsetOpen A r f
    ∀ (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (n : ℤ) (s : principalSubsetCoordinates A r f J n),
      (H.map (K.D₁ (ComplexShape.up ℤ) n (n + 1)))
        (principalSubsetInsertion A r f J n s) =
      principalSubsetInsertion A r f J (n + 1) (fun S ↦
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) (s ⟨S.val.erase j.val, h⟩))
          else 0) := by sorry

end AlgebraicGeometry
