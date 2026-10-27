/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.CategoryTheory.CondensedInternalBarData
import Sheaf.CategoryTheory.CondensedGroupAlgebraExactForgetful
import Sheaf.CategoryTheory.CondensedFreeLinearizationTensor

/-! # Induced coordinates for diagonal free modules

Source: blueprint direct-image stability, paragraph (3), internal bar input,
step 4 (blueprint: lem-sfb-condensed-induced-coordinates).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction

namespace Profinite.CondensedAction.InternalBar

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The induced presentation of a family of diagonal free modules. It uses none of
the differentials or exactness assertions.
Source: continuous change of coordinates, blueprint paragraph (3)
(blueprint: lem-sfb-condensed-induced-coordinates). -/
structure InducedCoordinates (objects : ℕ → ActionModule R G)
    (freeIso : ∀ n : ℕ, (objects n).module ≅ freePower R G (n + 1)) where
  /-- The induced presentation, retaining the internal equivariant module. -/
  induced : ℕ → ActionModule R G
  /-- Its underlying module is A[G] ⊗_A A[G^n]. -/
  inducedIso : ∀ n : ℕ,
    (induced n).module ≅ freePower R G 1 ⊗ freePower R G n
  /-- Only the first factor is acted on, by left translation. -/
  induced_action : ∀ (n : ℕ) (S : Profinite.{u}) (g a : C(S, G))
      (y : sectionModule R (freePower R G n) S),
    onSections R (inducedIso n).hom S
      ((induced n).act S g (onSections R (inducedIso n).inv S
        (pureTensor R _ _ S (generator R G 1 S (fun _ ↦ a)) y))) =
      pureTensor R _ _ S (generator R G 1 S (fun _ ↦ g * a)) y
  /-- The change of coordinates is an isomorphism of equivariant modules. -/
  coordinates : ∀ n : ℕ, objects n ≅ induced n
  /-- It is the specified continuous homogeneous-to-inhomogeneous coordinate map. -/
  coordinates_generator : ∀ (n : ℕ) (S : Profinite.{u}) (x : Fin (n + 1) → C(S, G)),
    onSections R ((coordinates n).hom.val ≫ (inducedIso n).hom) S
        (basis R G (n + 1) (objects n) (freeIso n) S x) =
      pureTensor R _ _ S (generator R G 1 S (fun _ ↦ x 0))
        (generator R G n S (fun i ↦ (x i.castSucc)⁻¹ * x i.succ))


/-- The continuous homogeneous-to-inhomogeneous coordinate map linearizes to the
specified equivariant induced presentation for any diagonal free family.

Source: blueprint direct-image stability, paragraph (3), internal bar input, step 4
(blueprint: lem-sfb-condensed-induced-coordinates).

Proof:
1. On tuples define c(g_0,...,g_n)=(g_0,g_0⁻¹g_1,...,g_(n-1)⁻¹g_n).
The inverse takes (a,h_1,...,h_n) to (a,ah_1,...,ah_1...h_n). Finite products of
continuous multiplication and inversion give continuous maps. Cancellation proves
both composites are identities. At n=0 the empty tuple is the terminal space.
2. Free linearization and CondensedFreeLinearization.Comparison.tensor identify the
free object on G^(n+1) with A[G] tensor A[G^n]. Their generator formulas give exactly
the displayed formula for coordinates_generator.
3. Linearize left translation on G and use GroupAlgebra.exists_tensorActions to tensor
this action with the trivially acted-on A[G^n]. This defines induced and inducedIso;
the action's pure tensor normalization proves induced_action for every section y.
4. The first coordinate of c(ug) is ug_0 and each successive quotient is
(ug_i)⁻¹(ug_(i+1))=g_i⁻¹g_(i+1). Thus the free coordinate map and its inverse commute
with the actions. Equivariant_iff_on_generators extends these generator equations;
the two inverse underlying maps therefore form the equivariant coordinates isomorphism.
-/
theorem exists_inducedCoordinates (objects : ℕ → ActionModule R G)
    (freeIso : ∀ n : ℕ, (objects n).module ≅ freePower R G (n + 1))
    (diagonal : ∀ (n : ℕ) (S : Profinite.{u}) (g : C(S, G))
      (x : Fin (n + 1) → C(S, G)),
      (objects n).act S g (basis R G (n + 1) (objects n) (freeIso n) S x) =
        basis R G (n + 1) (objects n) (freeIso n) S (fun i ↦ g * x i)) :
    Nonempty (InducedCoordinates R G objects freeIso) := by sorry

end Profinite.CondensedAction.InternalBar
