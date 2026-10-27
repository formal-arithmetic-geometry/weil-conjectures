/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.CondensedInternalBarData

public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.SheafTensorStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
public import Mathlib.Combinatorics.Quiver.ReflQuiver

import Sheaf.CategoryTheory.CondensedGroupAlgebraExactForgetful
import Sheaf.CategoryTheory.PointedFreeDeletionContraction
import Sheaf.CategoryTheory.CondensedEquivariantDeletionComparison
import Sheaf.CategoryTheory.CondensedInducedCoordinates

/-! # The augmented internal homogeneous bar resolution

Source: blueprint, direct-image stability, paragraph (3), formal internal bar input
(blueprint: lem-sfb-condensed-internal-bar-resolution).

Free objects are the actual composite of free abelian sheaf and free internal module.
The resolution specification retains all generator formulas, including the equivariant
induced presentation. No object is selected from the postponed existence theorem.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction
open scoped TensorProduct

namespace Profinite.CondensedAction.InternalBar

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
variable (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- A normalized model of the internal homogeneous bar resolution. All objects are
identified with the actual free objects, and all maps and actions are fixed on their
local generators. Tensoring is the internal relative tensor, with trivial action on T.
The final equivariant isomorphism is fixed by the displayed change of coordinates.
Source: all clauses of the augmented internal bar statement
(blueprint: lem-sfb-condensed-internal-bar-resolution). -/
structure Resolution where
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
  /-- Exactness at P_0 in the category of internal equivariant modules. -/
  exact_zero : (ShortComplex.mk (boundary 0) augmentation boundary_augmentation).Exact
  /-- Exactness at every P_(n+1), as image equals kernel. -/
  exact_succ : ∀ n : ℕ,
    (ShortComplex.mk (boundary (n + 1)) (boundary n) (boundary_boundary n)).Exact
  /-- Exactness at A, equivalently surjectivity of the augmentation. -/
  augmentation_epi : Epi augmentation
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
  /-- Tensor exactness at degree zero, without any flatness hypothesis on T. -/
  tensor_exact_zero : ∀ T : Modules R,
    (ShortComplex.mk (tensorBoundary T 0) (tensorAugmentation T)
      (tensor_boundary_augmentation T)).Exact
  /-- Tensor exactness at every positive degree. -/
  tensor_exact_succ : ∀ (T : Modules R) (n : ℕ),
    (ShortComplex.mk (tensorBoundary T (n + 1)) (tensorBoundary T n)
      (tensor_boundary_boundary T n)).Exact
  /-- Tensor exactness at T, including epimorphic augmentation. -/
  tensor_augmentation_epi : ∀ T : Modules R, Epi (tensorAugmentation T)
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

/-- The augmented internal homogeneous bar resolution is exact, remains exact after
internal tensoring with every module, and has the normalized equivariant induced
presentation. The normalized specification supplies actual free objects and maps;
no categorical projectivity is asserted.

Source: blueprint direct-image stability, paragraph (3), formal internal bar input
(blueprint: lem-sfb-condensed-internal-bar-resolution).

Proof:
1. Use the fixed internal-to-sectionwise module equivalence and its normalized tensor
comparison. Free modules are obtained by free abelian sheafification followed by the
free internal module functor. The adjunction identifies maps with assignments of local
sections to generators, so equalities may be checked on generators.
2. Sectionwise bilinear extension and module sheafification identify A[X] ⊗ A[Y] with
A[X × Y], sending [x] ⊗ [y] to [(x,y)]. The inverse respects the tensor relations.
3. Linearize diagonal multiplication and coordinate deletion. These maps commute with
all restrictions and the group action. The augmentation sends each generator to 1.
4. Two successive deletions of positions i < j occur with signs (-1)^(i+j) and
(-1)^(i+j-1), so they cancel. In degree zero the augmentation gives 1 - 1 = 0.
5. After forgetting the action, insert 1 as the first coordinate. With h_(-1)(a) = a[1],
this gives epsilon h_(-1) = id and d h + h d = id, also in degree zero where
d h[g] = [g] - [1]. These maps are not claimed equivariant.
6. A kernel inclusion k therefore satisfies k = d h k, proving kernel equals image.
The augmentation is split epimorphic on underlying modules.
7. Linearize the group law on A[G]; its module objects are precisely the internal
G-equivariant A-modules. Bilinear extension through sheafification constructs the
corresponding action on arbitrary module sections.
8. Internal tensor is additive and closed; tensoring with A[G] preserves finite colimits.
The generic module-object kernel, cokernel and abelianness results show that the
forgetful functor creates kernels and cokernels and reflects exactness. Hence the
underlying contraction proves exactness in the equivariant category as well.
9. Tensor the contraction with any T. Additivity preserves all contracting identities,
without flatness of T, and step 8 gives equivariant tensor exactness and surjectivity.
10. The continuous coordinates (g_0,...,g_n) ↦
(g_0,g_0^(-1)g_1,...,g_(n-1)^(-1)g_n) have inverse
(a,h_1,...,h_n) ↦ (a,ah_1,...,ah_1...h_n). They carry diagonal multiplication to
translation on the first factor alone. Free linearization and step 2 yield the
normalized equivariant induced isomorphism in every degree, including degree zero.
-/
theorem exists_resolution : Nonempty (Resolution R G) := by
  classical
  obtain ⟨c⟩ := PointedDeletion.exists_natural_contraction R
  obtain ⟨d⟩ := exists_deletionComparison R G c
  obtain ⟨i⟩ := exists_inducedCoordinates R G d.objects d.freeIso d.diagonal
  have ex := GroupAlgebra.exact_iff R G
  have e0 := (ex.1 _).mpr
    ((ShortComplex.exact_iff_of_iso d.zeroIso).mpr (c.data _ (identityPoint G)).exact_zero)
  have es (n : ℕ) := (ex.1 _).mpr
    ((ShortComplex.exact_iff_of_iso (d.succIso n)).mpr
      ((c.data _ (identityPoint G)).exact_succ n))
  have ep : Epi d.augmentation := (ex.2 _ _ _).mpr
    (((ShortComplex.exact_and_epi_g_iff_of_iso d.zeroIso).mpr
      ⟨(c.data _ (identityPoint G)).exact_zero,
        (c.data _ (identityPoint G)).augmentation_epi⟩).2)
  have te0 (T : Modules R) := (ex.1 _).mpr
    ((ShortComplex.exact_iff_of_iso (d.tensorZeroIso T)).mpr
      ((c.data _ (identityPoint G)).tensor_exact_zero T))
  have tes (T : Modules R) (n : ℕ) := (ex.1 _).mpr
    ((ShortComplex.exact_iff_of_iso (d.tensorSuccIso T n)).mpr
      ((c.data _ (identityPoint G)).tensor_exact_succ T n))
  have tep (T : Modules R) : Epi (d.tensorAugmentation T) := (ex.2 _ _ _).mpr
    (((ShortComplex.exact_and_epi_g_iff_of_iso (d.tensorZeroIso T)).mpr
      ⟨(c.data _ (identityPoint G)).tensor_exact_zero T,
        (c.data _ (identityPoint G)).tensor_augmentation_epi T⟩).2)
  exact ⟨{
    objects := d.objects
    freeIso := d.freeIso
    diagonal := d.diagonal
    augmentation := d.augmentation
    augmentation_generator := d.augmentation_generator
    boundary := d.boundary
    boundary_generator := d.boundary_generator
    boundary_augmentation := d.boundary_augmentation
    boundary_boundary := d.boundary_boundary
    exact_zero := e0
    exact_succ := es
    augmentation_epi := ep
    tensorObjects := d.tensorObjects
    tensorIso := d.tensorIso
    tensor_action := d.tensor_action
    tensorAugmentation := d.tensorAugmentation
    tensorAugmentation_underlying := d.tensorAugmentation_underlying
    tensorBoundary := d.tensorBoundary
    tensorBoundary_underlying := d.tensorBoundary_underlying
    tensor_boundary_augmentation := d.tensor_boundary_augmentation
    tensor_boundary_boundary := d.tensor_boundary_boundary
    tensor_exact_zero := te0
    tensor_exact_succ := tes
    tensor_augmentation_epi := tep
    induced := i.induced
    inducedIso := i.inducedIso
    induced_action := i.induced_action
    coordinates := i.coordinates
    coordinates_generator := i.coordinates_generator }⟩

end Profinite.CondensedAction.InternalBar
