/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.UniformFiniteFilteredLocalization
public import WeilConjectures.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.AlgebraicGeometry.FiniteFilteredGradedExactness
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.CategoryTheory.DgAbcHomotopyCategoryTriangulated
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Cochain bounds in uniformly finite filtered localizations

Source: Stacks Project, Derived Categories, Tags 05S5 and 05S6, with Tag 05S4,
restricted to uniformly finite filtrations and to each fixed filtration interval
(blueprint: lem-trf-filtered-bounded-localization-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Good lower truncation with the quotient filtration, computed as the image of
all subcomplex steps under the canonical projection. Source: Stacks, Tag 05S5(1)
(blueprint: lem-trf-filtered-bounded-localization-comparison). -/
def uniformFilteredTruncGE (K : FilteredObject (CochainComplex C ℤ)) (c : ℤ) :
    FilteredObject (CochainComplex C ℤ) where
  obj := K.obj.truncGE c
  filtration := K.filtration.image (K.obj.πTruncGE c)

/-- The canonical filtered lower-truncation projection. Source: Stacks, Tag 05S5(1)
(blueprint: lem-trf-filtered-bounded-localization-comparison). -/
def uniformFilteredTruncGEπ (K : FilteredObject (CochainComplex C ℤ)) (c : ℤ) :
    K ⟶ uniformFilteredTruncGE K c where
  hom := K.obj.πTruncGE c
  preserves p := ⟨factorThruImageSubobject
    ((K.filtration.F p).arrow ≫ K.obj.πTruncGE c), imageSubobject_arrow_comp _⟩

/-- Good upper truncation with its induced subobject filtration, the inverse image
of every original subcomplex step under the canonical inclusion.
Source: Stacks, Tag 05S5(2)
(blueprint: lem-trf-filtered-bounded-localization-comparison). -/
def uniformFilteredTruncLE (K : FilteredObject (CochainComplex C ℤ)) (d : ℤ) :
    FilteredObject (CochainComplex C ℤ) where
  obj := K.obj.truncLE d
  filtration :=
    { F := fun p ↦ (Subobject.pullback (K.obj.ιTruncLE d)).obj (K.filtration.F p)
      F_succ_le := fun p ↦ leOfHom ((Subobject.pullback (K.obj.ιTruncLE d)).map
        (homOfLE (K.filtration.F_succ_le p))) }

/-- The canonical filtered upper-truncation inclusion. Source: Stacks, Tag 05S5(2)
(blueprint: lem-trf-filtered-bounded-localization-comparison). -/
def uniformFilteredTruncLEι (K : FilteredObject (CochainComplex C ℤ)) (d : ℤ) :
    uniformFilteredTruncLE K d ⟶ K where
  hom := K.obj.ιTruncLE d
  preserves p := ⟨Subobject.pullbackπ (K.obj.ιTruncLE d) (K.filtration.F p),
    (Subobject.isPullback (K.obj.ιTruncLE d) (K.filtration.F p)).w⟩

/-- Full embeddings, their essential images, and canonical bounded representatives.
`none` means all uniformly finite filtrations; `some (a,b)` fixes `Fᵃ = K`, `Fᵇ⁺¹ = 0`.
The five comparisons are respectively bounded, below, and above into unbounded,
and bounded into below and above. Support bounds are common to every graded piece.

Source: Stacks, Tags 05S5 and 05S6, restricted to uniformly finite filtrations.
Proof (the eleven steps of the DAG node):
1. If graded cohomology below `c` vanishes, apply
   `lem-trf-finite-filtered-graded-exactness` at degree `c-1`. Strictness of
   `d^(c-1)` identifies the grade of its cokernel with the cokernel of its grade.
   Thus grading the lower good truncation gives the good truncation of each grade.
   The cohomology formula in `def-kun-truncations` proves the projection is a
   graded quasi-isomorphism. Quotient filtrations retain both filtration bounds.
2. Dually, strictness of `d^d` at degree `d+1` identifies its graded kernel with
   the kernel of its grade. The upper good truncation inclusion is a graded
   quasi-isomorphism. Induced subobject filtrations retain both bounds.
3. Graded cohomology descends through localization, since it inverts the defining
   maps (`def-weil-abstract-derived-category`). Steps 1 and 2 give one-sided
   representatives. For support `[c,d]`, truncate below `c`, then above `d`;
   the second operation retains the zero terms below `c`, giving a bounded roof.
4. The filtered cylinder `K ⊕ C(1_K)` identifies homotopic maps after localization:
   its projection is a graded quasi-isomorphism, its two sections become the same
   inverse, and the homotopy extends the two maps to a map from the cylinder.
   The direct-sum filtration retains uniform and prescribed bounds. Hence chain
   and homotopy localizations agree by their universal properties.
5. On filtered complexes, the dg differential is `dh = d_L h - (-1)^r h d_K`.
   Finite direct sums, signed shifts and the cone with direct-sum filtration
   satisfy A, B and C of `lem-coef-dg-abc-homotopy-category-triangulated`.
   Its conclusion gives the cone triangulation on all four homotopy categories.
6. Grade-acyclic objects are closed under shifts and triangles by
   `lem-sf-derived-homology-long-exact`. The cone criterion
   `lem-pur-quasi-iso-cone-acyclic` identifies their cone class with graded
   quasi-isomorphisms. `lem-trf-triangulated-subcategory-cone-system` then gives
   both calculi of fractions, without enough-injective or projective assumptions.
7. For fullness below, represent an ambient arrow by a left roof, using
   `lem-pc-left-localization-fraction-representation`. Its denominator transfers
   the common cohomological lower bound to the middle complex. Postcompose with
   the lower truncation of step 1 to obtain a bounded-below roof.
8. For faithfulness below, use `lem-pc-left-localization-fraction-equality`.
   The common denominator transfers the bound to its common comparison object.
   Truncate that object below; the same equations now witness equality below.
9. For the above case, use `lem-pc-right-fraction-representation` and
   `lem-pc-right-fraction-common-refinement`. Precompose the roof or its common
   refinement with the upper good truncation of step 2.
10. Repeat the below argument inside the above category for the bounded-to-above
    comparison. Lower truncation retains its upper term bound. Compose to obtain
    bounded-to-unbounded full faithfulness. Cancel the fully faithful below-to-
    unbounded functor on Hom bijections to obtain bounded-to-below faithfulness
    and fullness. Step 3 now proves the three essential-image descriptions.
11. Every truncation, cylinder, finite sum, shift, cone and roof refinement retains
    the prescribed filtration interval. Apply the same argument within that
    interval, rather than assuming its localization is a full subcategory.
(blueprint: lem-trf-filtered-bounded-localization-comparison). -/
theorem uniformFiltered_bounded_localization_comparison
    (C : Type u) [Category.{v} C] [Abelian C] (B : Option (ℤ × ℤ)) :
    Nonempty ((uniformFilteredComparison (C := C) B
      (P := uniformCochainBounded) (R := fun _ ↦ True)
      (fun _ _ ↦ True.intro)).FullyFaithful) ∧
    Nonempty ((uniformFilteredComparison (C := C) B
      (P := CochainComplex.plus C) (R := fun _ ↦ True)
      (fun _ _ ↦ True.intro)).FullyFaithful) ∧
    Nonempty ((uniformFilteredComparison (C := C) B
      (P := CochainComplex.minus C) (R := fun _ ↦ True)
      (fun _ _ ↦ True.intro)).FullyFaithful) ∧
    Nonempty ((uniformFilteredComparison (C := C) B
      (P := uniformCochainBounded) (R := CochainComplex.plus C)
      (fun _ h ↦ h.1)).FullyFaithful) ∧
    Nonempty ((uniformFilteredComparison (C := C) B
      (P := uniformCochainBounded) (R := CochainComplex.minus C)
      (fun _ h ↦ h.2)).FullyFaithful) ∧
    (∀ X : UniformFilteredDerived C B (fun _ ↦ True),
      (uniformFilteredComparison B (P := uniformCochainBounded) (R := fun _ ↦ True)
        (fun _ _ ↦ True.intro)).essImage X ↔
        ∃ c d : ℤ, c ≤ d ∧ uniformLocalizedSupport B (Set.Icc c d) X) ∧
    (∀ X : UniformFilteredDerived C B (fun _ ↦ True),
      (uniformFilteredComparison B (P := CochainComplex.plus C) (R := fun _ ↦ True)
        (fun _ _ ↦ True.intro)).essImage X ↔
        ∃ c : ℤ, uniformLocalizedSupport B (Set.Ici c) X) ∧
    (∀ X : UniformFilteredDerived C B (fun _ ↦ True),
      (uniformFilteredComparison B (P := CochainComplex.minus C) (R := fun _ ↦ True)
        (fun _ _ ↦ True.intro)).essImage X ↔
        ∃ d : ℤ, uniformLocalizedSupport B (Set.Iic d) X) ∧
    (∀ (K : UniformFilteredComplexes C B (fun _ ↦ True)) (c : ℤ),
      uniformGradedSupport (Set.Ici c) K.obj →
        (∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps
          (uniformFilteredTruncGEπ K.obj c) p)) ∧
        uniformFilteredProperty B (fun _ ↦ True) (uniformFilteredTruncGE K.obj c) ∧
        (∀ n : ℤ, n < c → IsZero ((K.obj.obj.truncGE c).X n)) ∧
        (∀ n : ℤ, c < n → IsIso ((K.obj.obj.πTruncGE c).f n))) ∧
    (∀ (K : UniformFilteredComplexes C B (fun _ ↦ True)) (d : ℤ),
      uniformGradedSupport (Set.Iic d) K.obj →
        (∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps
          (uniformFilteredTruncLEι K.obj d) p)) ∧
        uniformFilteredProperty B (fun _ ↦ True) (uniformFilteredTruncLE K.obj d) ∧
        (∀ n : ℤ, d < n → IsZero ((K.obj.obj.truncLE d).X n)) ∧
        (∀ n : ℤ, n < d → IsIso ((K.obj.obj.ιTruncLE d).f n))) := by
  sorry

end CategoryTheory
