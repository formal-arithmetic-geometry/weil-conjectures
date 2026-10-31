/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedInternalBarData
public import WeilConjectures.CategoryTheory.PointedFreeDeletionContraction
public import WeilConjectures.CategoryTheory.CondensedGroupAlgebraExactForgetful

/-! # Equivariant linearization of the deletion complex

Source: blueprint direct-image stability, paragraph (3), internal bar input,
steps 1--3 (blueprint: lem-sfb-condensed-equivariant-deletion-comparison).
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

/-- The identity section of the represented condensed group.
Source: insertion of the identity in the bar contraction
(blueprint: lem-sfb-condensed-equivariant-deletion-comparison). -/
def identityPoint : ⊤_ PointedDeletion.Sets.{u} ⟶ GroupAlgebra.groupSet G where
  hom :=
    { app := fun S ↦ ↾fun _ ↦ ULift.up
        (CompHausLike.ofHom _ ⟨fun _ : S.unop ↦ (1 : G), continuous_const⟩)
      naturality := by intros; rfl }

/-- The normalized equivariant complex, before asserting exactness or an induced
presentation. All generator formulas and actual tensor maps are retained.
Source: linearization of coordinate deletion, blueprint paragraph (3)
(blueprint: lem-sfb-condensed-equivariant-deletion-comparison). -/
structure EquivariantComplex where
  /-- The equivariant terms. -/
  objects : ℕ → ActionModule R G
  /-- P_n is the actual free module on G^(n+1), up to specified isomorphism. -/
  freeIso : ∀ n : ℕ, (objects n).module ≅ freePower R G (n + 1)
  /-- The action is diagonal left multiplication, for every continuous local parameter. -/
  diagonal : ∀ (n : ℕ) (S : Profinite.{u}) (g : C(S, G))
      (x : Fin (n + 1) → C(S, G)),
    (objects n).act S g (basis R G (n + 1) (objects n) (freeIso n) S x) =
      basis R G (n + 1) (objects n) (freeIso n) S (fun i ↦ g * x i)
  /-- The augmentation to the regular module with trivial action is equivariant. -/
  augmentation : objects 0 ⟶ (trivial (R := R) (P := G)).obj (Mod.regular R.X)
  /-- Every generator goes to the unit section. -/
  augmentation_generator : ∀ (S : Profinite.{u}) (x : Fin 1 → C(S, G)),
    onSections R augmentation.val S (basis R G 1 (objects 0) (freeIso 0) S x) =
      regularOne R S
  /-- Equivariant boundary morphisms. -/
  boundary : ∀ n : ℕ, objects (n + 1) ⟶ objects n
  /-- The boundary is the alternating sum of coordinate deletions. -/
  boundary_generator : ∀ (n : ℕ) (S : Profinite.{u}) (x : Fin (n + 2) → C(S, G)),
    onSections R (boundary n).val S
        (basis R G (n + 2) (objects (n + 1)) (freeIso (n + 1)) S x) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        basis R G (n + 1) (objects n) (freeIso n) S (fun j ↦ x (i.succAbove j))
  /-- The first boundary composes with the augmentation to zero. -/
  boundary_augmentation : boundary 0 ≫ augmentation = 0
  /-- Successive boundaries compose to zero in every degree. -/
  boundary_boundary : ∀ n : ℕ, boundary (n + 1) ≫ boundary n = 0
  /-- Terms after tensoring with an arbitrary module with trivial group action. -/
  tensorObjects : Modules R → ℕ → ActionModule R G
  /-- The underlying object is the internal relative tensor product. -/
  tensorIso : ∀ (T : Modules R) (n : ℕ),
    (tensorObjects T n).module ≅ (objects n).module ⊗ T
  /-- The tensor action acts on the first factor and fixes the second. -/
  tensor_action : ∀ (T : Modules R) (n : ℕ) (S : Profinite.{u}) (g : C(S, G))
      (x : sectionModule R (objects n).module S) (t : sectionModule R T S),
    onSections R (tensorIso T n).hom S
      ((tensorObjects T n).act S g
        (onSections R (tensorIso T n).inv S (pureTensor R _ T S x t))) =
      pureTensor R _ T S ((objects n).act S g x) t
  /-- The tensored augmentation, as an equivariant arrow. -/
  tensorAugmentation : ∀ T : Modules R, tensorObjects T 0 ⟶ (trivial (R := R) (P := G)).obj T
  /-- Tensor the original augmentation and apply the unit identification A ⊗ T ≅ T. -/
  tensorAugmentation_underlying : ∀ T : Modules R,
    (tensorAugmentation T).val =
      (tensorIso T 0).hom ≫ augmentation.val ▷ T ≫ (λ_ T).hom
  /-- The tensored boundaries, as equivariant arrows. -/
  tensorBoundary : ∀ (T : Modules R) (n : ℕ),
    tensorObjects T (n + 1) ⟶ tensorObjects T n
  /-- The boundary is precisely the original boundary tensored with the identity. -/
  tensorBoundary_underlying : ∀ (T : Modules R) (n : ℕ),
    (tensorBoundary T n).val =
      (tensorIso T (n + 1)).hom ≫ (boundary n).val ▷ T ≫ (tensorIso T n).inv
  /-- The tensored augmentation is a complex. -/
  tensor_boundary_augmentation : ∀ T : Modules R,
    tensorBoundary T 0 ≫ tensorAugmentation T = 0
  /-- The tensored differentials compose to zero. -/
  tensor_boundary_boundary : ∀ (T : Modules R) (n : ℕ),
    tensorBoundary T (n + 1) ≫ tensorBoundary T n = 0

/-- Comparison with the pointed deletion complex after forgetting the action.
Source: free linearization of finite powers, blueprint paragraph (3)
(blueprint: lem-sfb-condensed-equivariant-deletion-comparison). -/
structure DeletionComparison (c : PointedDeletion.NaturalContraction R)
    extends EquivariantComplex R G where
  /-- The augmentation diagram agrees with the pointed free complex. -/
  zeroIso :
    (ShortComplex.mk (boundary 0) augmentation boundary_augmentation).map forgetAction ≅
      ShortComplex.mk (PointedDeletion.boundary R (GroupAlgebra.groupSet G) 0)
        (c.data _ (identityPoint G)).augmentation
        (c.data _ (identityPoint G)).boundary_augmentation
  /-- Agreement of the positive-degree diagrams. -/
  succIso : ∀ n : ℕ,
    (ShortComplex.mk (boundary (n + 1)) (boundary n) (boundary_boundary n)).map
      forgetAction ≅
      ShortComplex.mk (PointedDeletion.boundary R (GroupAlgebra.groupSet G) (n + 1))
        (PointedDeletion.boundary R (GroupAlgebra.groupSet G) n)
        ((c.data _ (identityPoint G)).boundary_boundary n)
  /-- The augmentation comparison after tensoring with any internal module. -/
  tensorZeroIso : ∀ T : Modules R,
    (ShortComplex.mk (tensorBoundary T 0) (tensorAugmentation T)
      (tensor_boundary_augmentation T)).map forgetAction ≅
      ShortComplex.mk (PointedDeletion.boundary R (GroupAlgebra.groupSet G) 0 ▷ T)
        ((c.data _ (identityPoint G)).augmentation ▷ T ≫ (λ_ T).hom)
        ((c.data _ (identityPoint G)).tensor_boundary_augmentation T)
  /-- The positive-degree comparison after tensoring. -/
  tensorSuccIso : ∀ (T : Modules R) (n : ℕ),
    (ShortComplex.mk (tensorBoundary T (n + 1)) (tensorBoundary T n)
      (tensor_boundary_boundary T n)).map forgetAction ≅
      ShortComplex.mk (PointedDeletion.boundary R (GroupAlgebra.groupSet G) (n + 1) ▷ T)
        (PointedDeletion.boundary R (GroupAlgebra.groupSet G) n ▷ T)
        ((c.data _ (identityPoint G)).tensor_boundary_boundary T n)

/-- Linearizing diagonal multiplication gives the normalized equivariant deletion
complex and its comparison with the existing pointed deletion complex. This asserts
no exactness and no homogeneous-to-inhomogeneous coordinate isomorphism.

Source: blueprint direct-image stability, paragraph (3), internal bar input, steps
1--3 (blueprint: lem-sfb-condensed-equivariant-deletion-comparison).

Proof:
1. For each n use the canonical isomorphism between the representable sheaf of G^n
and the categorical n-fold power of the representable sheaf of G. Both directions
send a continuous tuple to its coordinate maps; they are inverse, including n=0.
Apply the free functor to these isomorphisms.
2. Apply GroupAlgebra.linearization_exists to diagonal multiplication on represented
powers. Multiplication is continuous and commutes with restriction; the identity and
product laws hold coordinatewise. This constructs objects and their freeIso maps.
3. Transport the pointed deletion augmentation and alternating boundaries along these
free isomorphisms. Deletion commutes with diagonal multiplication, so
GroupAlgebra.linearization_map and equivariant_closure give equivariant boundaries.
The augmentation is equivariant by equivariant_iff_on_generators, since it sends every
generator to 1. The contraction's generator formulas give the displayed formulas.
4. The comparison squares identify the underlying augmented short complexes, so the
two complex identities follow from the pointed deletion complex identities and
faithfulness of forgetting. These squares give zeroIso and succIso.
5. Use GroupAlgebra.exists_tensorActions for the actual internal tensor actions.
Tensor each equivariant boundary; tensor the augmentation and compose with the left
unitor. The latter is equivariant because its source has the tensor of two trivial
actions. Check this on pure tensors and use the internal tensor universal property.
Naturality of the tensor action comparisons gives the specified underlying formulas,
complex identities, and tensorZeroIso/tensorSuccIso. No exactness is used here.
-/
theorem exists_deletionComparison (c : PointedDeletion.NaturalContraction R) :
    Nonempty (DeletionComparison R G c) := by sorry

end Profinite.CondensedAction.InternalBar
