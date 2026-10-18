/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-! # Finite filtered graded exactness

Source: Stacks Project, Homology, Tag 05QH, lemma-filtered-acyclic,
parts (1)--(5), with the finite filtrations of Tag 0121
(blueprint: lem-trf-finite-filtered-graded-exactness).

The filtered objects, filtration-preserving maps, filtration steps, graded pieces and the
canonical step and graded maps are the recorded ones of `def-sp-filtration`
(`CategoryTheory.FilteredObject` over `CategoryTheory.DecreasingFiltration`, with
`FilteredObject.restrictionSteps` and `FilteredObject.gradedMapSteps`).

## Main definitions

- `CategoryTheory.FilteredObject.IsStrict`: strict filtered maps.
- `CategoryTheory.FilteredObject.quotientObject`, `CategoryTheory.FilteredObject.quotientMap`:
  the quotients `A/FᵖA` and the induced maps.

## Main statements

- `CategoryTheory.FilteredObject.finite_filtered_graded_exactness`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredObject

/-- A filtered map `f : M → N` is strict when `f(FᵖM) = im(f) ∩ FᵖN` for every
integer `p`, as subobjects of `N`.
Source: Stacks Project, Homology, Tag 05QH, part (4)
(blueprint: lem-trf-finite-filtered-graded-exactness). -/
def IsStrict {A B : FilteredObject C} (f : A ⟶ B) : Prop :=
  ∀ p : ℤ,
    imageSubobject (restrictionSteps f p ≫ (B.filtration.step p).arrow) =
      imageSubobject f.hom ⊓ B.filtration.step p

/-- The `p`-th quotient object `A/FᵖA` of a filtered object: the cokernel of the
inclusion of the `p`-th filtration step.
Source: Stacks Project, Homology, Tag 05QH, part (3)
(blueprint: lem-trf-finite-filtered-graded-exactness). -/
noncomputable def quotientObject (A : FilteredObject C) (p : ℤ) : C :=
  cokernel (A.filtration.step p).arrow

/-- A filtered map composed with the projection onto `B/FᵖB` kills `FᵖA`.
Source: Stacks Project, Homology, Tag 05QH, part (3)
(blueprint: lem-trf-finite-filtered-graded-exactness).

Proof: by `f.preserves p`, the inclusion `FᵖA → A` followed by `f` factors through
the inclusion `FᵖB → B`, which the cokernel projection of `B` kills. -/
theorem quotientMap_condition {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    (A.filtration.step p).arrow ≫ f.hom ≫
      cokernel.π (B.filtration.step p).arrow = 0 := by
  sorry

/-- The map `A/FᵖA → B/FᵖB` induced by a filtered map, by the cokernel universal
property.
Source: Stacks Project, Homology, Tag 05QH, part (3)
(blueprint: lem-trf-finite-filtered-graded-exactness). -/
noncomputable def quotientMap {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    quotientObject A p ⟶ quotientObject B p :=
  cokernel.desc (A.filtration.step p).arrow
    (f.hom ≫ cokernel.π (B.filtration.step p).arrow)
    (quotientMap_condition f p)

/-- The induced quotient maps of a filtered complex `vu = 0` compose to zero.
Source: Stacks Project, Homology, Tag 05QH, part (3)
(blueprint: lem-trf-finite-filtered-graded-exactness).

Proof: precompose with the epimorphic cokernel projection of `X`; by the two
`cokernel.π_desc` equations the composite becomes `u ≫ v ≫ π = 0`. -/
theorem quotientMap_comp {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0) (p : ℤ) :
    quotientMap u p ≫ quotientMap v p = 0 := by
  sorry

/-- The induced maps on `p`-th filtration steps of a filtered complex `vu = 0`
compose to zero.
Source: Stacks Project, Homology, Tag 05QH, part (2)
(blueprint: lem-trf-finite-filtered-graded-exactness).

Proof: postcompose with the monic inclusion `FᵖZ → Z`; by the defining equations of
`restrictionSteps` the composite becomes `FᵖX → X` followed by `u ≫ v = 0`. -/
theorem restrictionSteps_comp {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0) (p : ℤ) :
    restrictionSteps u p ≫ restrictionSteps v p = 0 := by
  sorry

/-- The induced maps on `p`-th graded pieces of a filtered complex `vu = 0` compose
to zero.
Source: Stacks Project, Homology, Tag 05QH, parts (1)--(3)
(blueprint: lem-trf-finite-filtered-graded-exactness).

Proof: precompose with the epimorphic cokernel projection `FᵖX → grᵖX`; by
`exists_gradedMap_steps` the composite becomes the composite of the restrictions
followed by a projection, which vanishes by `restrictionSteps_comp`. -/
theorem gradedMapSteps_comp {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (hvu : u.hom ≫ v.hom = 0) (p : ℤ) :
    gradedMapSteps u p ≫ gradedMapSteps v p = 0 := by
  sorry

/-- Graded exactness implies strict exactness for finite filtered objects: for
filtration-preserving maps `X → Y → Z` of finitely filtered objects with `vu = 0` and
exact `grᵖX → grᵖY → grᵖZ` for every `p`, the maps `u` and `v` are strict, `X → Y → Z`
is exact, and for every `p` both `FᵖX → FᵖY → FᵖZ` and `X/FᵖX → Y/FᵖY → Z/FᵖZ` are exact.

Source: Stacks Project, Homology, Tag 05QH, lemma-filtered-acyclic, parts (1)--(5)
(blueprint: lem-trf-finite-filtered-graded-exactness).

Proof.
1. Choose common integers `a ≤ b` with `FᵃT = T` and `FᵇT = 0` for `T = X, Y, Z`: `a` the
   minimum of the three whole-object bounds, `b` the maximum of `a` and the three zero
   bounds [def-sp-filtration]. Put `K = (X → Y → Z)` in degrees `0, 1, 2`. As `vu = 0`
   it is a complex; filtration preservation makes each `FᵖK` a subcomplex, and `K/FᵖK`,
   `grᵖK = FᵖK/Fᵖ⁺¹K` carry the induced differentials. `H¹` of a three-term complex is
   the kernel of the second map modulo the image of the first, so the hypothesis says
   `H¹(grᵖK) = 0` for every `p`.
2. Prove `H¹(FᵖK) = 0` by descending induction from `b` (zero for `p ≥ b`). The sequence
   `0 → Fᵖ⁺¹K → FᵖK → grᵖK → 0` is termwise short exact; the long exact sequence
   [lem-weil-pbc-complex-ses-homology-long-exact]
   (`CategoryTheory.ShortComplex.ShortExact.homology_exact₂`) gives the exact segment
   `H¹(Fᵖ⁺¹K) → H¹(FᵖK) → H¹(grᵖK)` with zero outside terms. For `p ≤ a` the complex is
   `K`. So every `FᵖX → FᵖY → FᵖZ` is exact, and `p = a` gives exactness of `X → Y → Z`.
3. Prove `H¹(K/FᵖK) = 0` by ascending induction from `a` (zero for `p ≤ a`). The sequence
   `0 → grᵖK → K/Fᵖ⁺¹K → K/FᵖK → 0` is termwise short exact; the long exact sequence
   [lem-weil-pbc-complex-ses-homology-long-exact] gives the exact segment
   `H¹(grᵖK) → H¹(K/Fᵖ⁺¹K) → H¹(K/FᵖK)` with zero outside terms. Above `b` the quotient is
   `K`, exact by Step 2. So every `X/FᵖX → Y/FᵖY → Z/FᵖZ` is exact.
4. Strictness of `u`: as subobjects of `Y`,
   `u(FᵖX) = ker(v|FᵖY) = ker(v) ∩ FᵖY = im(u) ∩ FᵖY`, by step exactness, the pullback
   description of the kernel along `FᵖY → Y`, and underlying exactness.
5. Strictness of `v`: with `q : Y → Y/FᵖY` and the induced `ū, v̄`, the square defining
   `v̄` gives `v⁻¹(FᵖZ) = q⁻¹(ker v̄)`; quotient exactness gives
   `ker v̄ = im ū = q(im u)`, as `X → X/FᵖX` is epi. Hence `v⁻¹(FᵖZ) = FᵖY + im u`, and
   `im(v) ∩ FᵖZ = v(v⁻¹(FᵖZ)) = v(FᵖY + im u) = v(FᵖY)` because `vu = 0`. These are
   subobject inverse-image, sum and image identities; no element is lifted. -/
theorem finite_filtered_graded_exactness
    {X Y Z : FilteredObject C}
    (u : X ⟶ Y) (v : Y ⟶ Z)
    (hvu : u.hom ≫ v.hom = 0)
    (hX : DecreasingFiltration.IsFinite X.filtration)
    (hY : DecreasingFiltration.IsFinite Y.filtration)
    (hZ : DecreasingFiltration.IsFinite Z.filtration)
    (hgr : ∀ p : ℤ,
      (ShortComplex.mk (gradedMapSteps u p) (gradedMapSteps v p)
        (gradedMapSteps_comp u v hvu p)).Exact) :
    FilteredObject.IsStrict u ∧
      FilteredObject.IsStrict v ∧
      (ShortComplex.mk u.hom v.hom hvu).Exact ∧
      (∀ p : ℤ,
        (ShortComplex.mk (restrictionSteps u p) (restrictionSteps v p)
          (restrictionSteps_comp u v hvu p)).Exact ∧
        (ShortComplex.mk (quotientMap u p) (quotientMap v p)
          (quotientMap_comp u v hvu p)).Exact) := by
  sorry

end FilteredObject

end CategoryTheory
