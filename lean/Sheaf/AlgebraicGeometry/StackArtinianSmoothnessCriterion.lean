/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.MarkedStackDeformations
public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Sheaf.RingTheory.AdicFormalSmoothnessDescent

/-! # Artinian deformation criterion for smoothness of an algebraic stack

Source: Stacks Project, Geometry of Algebraic Stacks, Tag 0DZS,
lemma-characterize-smoothness, equivalence (1) and (3), using Tag 0DQX
for existence of a versal ring
(blueprint: lem-sfb-stack-artinian-smoothness-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.StackDeformation

/-- A residue-field point lies in the largest smooth open substack exactly when
all its marked Artinian deformations lift across every surjection. The left side
specifies the largest open by its universal property, without choosing it. On the
right `PullsBack` includes the isomorphism respecting the specified markings.

Source: Stacks Project, Geometry of Algebraic Stacks, Tag 0DZS,
lemma-characterize-smoothness, equivalence (1) and (3); Tag 0DQX
(blueprint: lem-sfb-stack-artinian-smoothness-criterion).

Proof following the five steps of the node:
1. By lem-sfb-stack-versal-ring-existence choose a versal ring C at x. The base
is Noetherian local and Spec k is its closed point, hence finite type. By
lem-sfb-stack-maximal-smooth-open the largest smooth open exists.
2. The right side is unobstructedness of the marked deformation groupoid.
Its fibre at k is nonempty and has exactly one arrow between any two objects:
for markings alpha and beta it is beta inverse composed with alpha. Apply
lem-sfb-versal-unobstructed-adic-criterion to identify unobstructedness with
adic formal smoothness of R -> C.
3. Choose a smooth surjective scheme atlas. By lem-sfb-stack-atlas-versal-completion
choose an affine chart V = Spec B and a point z over the closed point, a finite
common residue extension identifying its image with x, and the versal ring
D = completion of the local ring at z. That node also identifies membership of
x in the largest smooth open with smoothness of V -> Spec R at z.
4. By lem-sfb-stack-versal-ring-smooth-span find a common complete Noetherian
local ring H with adically formally smooth local maps C -> H and D -> H.
Apply lem-sfb-adic-formal-smoothness-descent to R -> C -> H and R -> D -> H.
Thus R -> C is adically formally smooth exactly when R -> D is; completeness
of R and separability of the residue extensions are unnecessary.
5. B is finite type over the Noetherian ring R and z lies over its closed point.
Apply lem-sfb-finite-type-completed-local-smoothness to identify adic formal
smoothness of R -> D with smoothness of V -> Spec R at z. Combine steps 2--4.
-/
theorem stack_artinian_smoothness_criterion
    (R k : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field k] [Algebra R k] (residueEquiv : IsLocalRing.ResidueField R ≃ₐ[R] k)
    (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (hF : IsAlgebraicModuliStack F)
    (hft : ∃ (U : Over (Spec (.of R)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧ LocallyOfFiniteType U.hom)
    (x : Functor.Fiber F.p (affine (CommAlgCat.of R k))) :
    (∃ U : OpenModuliSubstack F,
      IsSmoothModuliStack U.category ∧
      (∀ V : OpenModuliSubstack F,
        IsSmoothModuliStack V.category → V.IsContainedIn U) ∧ U.property x.val) ↔
    ∀ (A' A : ArtinDeformation.TestCategory R k) (q : A' ⟶ A),
      Function.Surjective (ArtinDeformation.map q) →
      ∀ Y : Marked F x A, ∃ Y' : Marked F x A', PullsBack F x q Y' Y := by
  sorry

end AlgebraicGeometry.StackDeformation
