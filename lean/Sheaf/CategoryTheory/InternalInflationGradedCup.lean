/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.CategoryTheory.CondensedProductActionInflation
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import Mathlib.CategoryTheory.Shift.ShiftedHom
import Sheaf.CategoryTheory.ActionToposGeometricRestriction
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.Paper.ShiftedTensorMorphismCalculus
import Sheaf.Algebra.Homology.DerivedTensorShiftDescent

/-! # Derived internal inflation and ordered graded cup composition

Source: main-20261015 six-functors direct-images proof, paragraph (3), the
agent-formulated internal bar normalization (exact internal-category reference wanted)
(blueprint: lem-sfb-internal-inflation-graded-cup).

The functors, invariant-inclusion adjunction, relative derived tensors and cup algebra
are the existing ones of `CondensedDerivedRestriction`. The helpers below merely spell
out the shifted adjunction and the fixed, first-then-second tensor-shift comparisons.
The universal sign is quantified before the ring, group and cohomology classes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (trivial)
namespace CategoryTheory.CondensedDerivedRestriction

/-- Assemble the shifted-unit comparison from its specified tensor-shift isomorphism.
This generic helper keeps the coefficient-category structures out of the shift arithmetic.
Source: paragraph (3), Stacks 0FNG (blueprint: lem-sfb-internal-inflation-graded-cup). -/
def shiftedUnitTensorFromComparison {D : Type v} [Category.{w} D] [MonoidalCategory D]
    [HasShift D ℤ] (I : D) (e : 𝟙_ D ≅ I) (p q : ℕ)
    (s : I⟦-(p : ℤ)⟧ ⊗ I⟦-(q : ℤ)⟧ ≅ (I ⊗ I)⟦-(p : ℤ) + -(q : ℤ)⟧) :
    I⟦-((p + q : ℕ) : ℤ)⟧ ≅ I⟦-(p : ℤ)⟧ ⊗ I⟦-(q : ℤ)⟧ :=
  eqToIso (congrArg (fun n : ℤ => I⟦n⟧) (by simp [add_comm])) ≪≫
    ((shiftFunctor D (-(p : ℤ) + -(q : ℤ))).mapIso
      (whiskerRightIso e.symm I ≪≫ λ_ I)).symm ≪≫ s.symm

variable (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The usual cochain shifts on exact derived trivial inflation.
Source: paragraph (3) (blueprint: lem-sfb-internal-inflation-graded-cup). -/
instance trivialDerivedShift : (trivialDerived A G).CommShift ℤ :=
  inferInstanceAs ((trivial (R := A.toMon) (P := G)).mapDerivedCategory.CommShift ℤ)

/-- Inflation of the actual regular module in degree zero, not an arbitrary unit map.
Source: paragraph (3) (blueprint: lem-sfb-internal-inflation-graded-cup). -/
def inflatedCoefficientIso :
    (trivialDerived A G).obj
      ((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)) ≅
        coefficient A G :=
  ((trivial (R := A.toMon) (P := G)).mapDerivedCategorySingleFunctor 0).app
    (Mod.regular A.X)

/-- Inflation of the negatively shifted coefficient object, using the usual cochain shift.
Source: paragraph (3) (blueprint: lem-sfb-internal-inflation-graded-cup). -/
def inflatedShiftedCoefficientIso (q : ℕ) :
    (trivialDerived A G).obj
      (((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X))⟦-(q : ℤ)⟧) ≅
        (coefficient A G)⟦-(q : ℤ)⟧ :=
  ((trivialDerived A G).commShiftIso (-(q : ℤ))).app _ ≪≫
    (shiftFunctor _ (-(q : ℤ))).mapIso (inflatedCoefficientIso A G)

/-- The shift adjunction converts a positive shifted endomorphism into a negative-source map.
Source: paragraph (3) (blueprint: lem-sfb-internal-inflation-graded-cup). -/
def negativelyShiftedArrow (q : ℕ)
    (x : coefficient A G ⟶ (coefficient A G)⟦(q : ℤ)⟧) :
    (coefficient A G)⟦-(q : ℤ)⟧ ⟶ coefficient A G :=
  ((shiftEquiv' (DerivedCategory.{u + 1} (Equivariant A G)) (-(q : ℤ)) (q : ℤ)
    (neg_add_cancel (q : ℤ))).toAdjunction.homEquiv _ _).symm x

/-- The specified shifted adjunction bijection Phi, with the invariant-inclusion adjunction.
Source: paragraph (3) (blueprint: lem-sfb-internal-inflation-graded-cup). -/
def inflationPhi (q : ℕ) :
    (coefficient A G ⟶ (coefficient A G)⟦(q : ℤ)⟧) ≃
      (((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X))⟦-(q : ℤ)⟧ ⟶
        cohomology A G) :=
  (((shiftEquiv' (DerivedCategory.{u + 1} (Equivariant A G)) (-(q : ℤ)) (q : ℤ)
      (neg_add_cancel (q : ℤ))).toAdjunction.homEquiv _ _).symm.trans
    (Iso.homCongr (inflatedShiftedCoefficientIso A G q).symm (Iso.refl _))).trans
      ((adjunction A G).homEquiv _ _)

/-- The fixed shifted regular-unit tensor comparison in the base category. It extracts
first the first shift, then the second, with the upstream signed cochain comparisons.
Source: paragraph (3), Stacks 0FNG (blueprint: lem-sfb-internal-inflation-graded-cup). -/
def baseShiftedUnitTensor (p q : ℕ) :
    (((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)))⟦-((p + q : ℕ) : ℤ)⟧ ≅
      (((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)))⟦-(p : ℤ)⟧ ⊗
        (((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)))⟦-(q : ℤ)⟧ :=
  shiftedUnitTensorFromComparison _ (baseUnitIso A) p q
    (DerivedCategory.shiftTensorShiftIso (Modules A) _ _ (-(p : ℤ)) (-(q : ℤ)))

/-- The identical extraction convention for shifted trivial regular coefficients in actions.
Source: paragraph (3), Stacks 0FNG (blueprint: lem-sfb-internal-inflation-graded-cup). -/
def actionShiftedUnitTensor (p q : ℕ) :
    (coefficient A G)⟦-((p + q : ℕ) : ℤ)⟧ ≅
      (coefficient A G)⟦-(p : ℤ)⟧ ⊗ (coefficient A G)⟦-(q : ℤ)⟧ :=
  shiftedUnitTensorFromComparison _ (actionUnitIso A G) p q
    (DerivedCategory.shiftTensorShiftIso (Equivariant A G) _ _ (-(p : ℤ)) (-(q : ℤ)))

/-- Cup on negatively shifted coefficient-source classes, with no interchange of factors.
Source: paragraph (3) (blueprint: lem-sfb-internal-inflation-graded-cup). -/
def inflationGradedCup (p q : ℕ)
    (a : (((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)))⟦-(p : ℤ)⟧ ⟶
      cohomology A G)
    (b : (((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)))⟦-(q : ℤ)⟧ ⟶
      cohomology A G) :
    (((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)))⟦-((p + q : ℕ) : ℤ)⟧ ⟶
      cohomology A G :=
  (baseShiftedUnitTensor A p q).hom ≫ (a ⊗ₘ b) ≫ cup (A := A) (G := G)

section ProfiniteGroup
variable [hCompact : CompactSpace G] [hHausdorff : T2Space G]
  [hDisconnected : TotallyDisconnectedSpace G]
include hCompact hHausdorff hDisconnected

/-- Exact strong symmetric monoidal inflation with its fixed tensor, unit and shift models.
Source: paragraph (3) (blueprint: lem-sfb-internal-inflation-graded-cup).
Proof: present condensed actions as modules on the small action site using
lem-sfb-action-topos-geometric-restriction. The ringed derived tensor theorem and
lem-sfb-ringed-derived-monoidal-comparisons give the signed symmetric strong comparison.
Exact inflation descends termwise by lem-weil-pbc-exact-functor-derived-factorization;
its K-flat comparisons are the uniquely normalized derivedTrivialTensor. The normalized
invariant-inclusion adjunction is adjunction A G. Grothendieck K-injective existence and
lem-sp-canonical-right-derived-adjunction-shift give compatibility with the usual shifts.
The localized ordinary identity tensor and unit comparisons give both model equations. -/
theorem internalInflationStructure :
    (trivialDerived A G).IsTriangulated ∧
    (∃ b : (trivialDerived A G).Braided,
      b.toMonoidal = derivedTrivialMonoidal (A := A) (G := G)) ∧
    TrivialTensorModel (A := A) (G := G) (derivedTrivialTensor A G) ∧
    TrivialUnitModel (A := A) (G := G) (derivedTrivialTensor A G) ∧
    (adjunction A G).CommShift ℤ := by
  sorry

/-- Phi sends the degree-zero identity to the actual cup unit, with zero-shift and
regular-unit identifications explicitly retained.
Source: paragraph (3) (blueprint: lem-sfb-internal-inflation-graded-cup).
Proof: the lax unit is the transpose of the inverse strong unit comparison, by
lem-sfb-monoidal-adjunction-mates. The ordinary unit normalization and the zero-shift
identity identify this transpose with the identity of the coefficient object. -/
theorem inflationPhiIdentity :
    inflationPhi A G 0 ((shiftFunctorZero _ ℤ).inv.app (coefficient A G)) =
      (shiftFunctorZero _ ℤ).hom.app
          ((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X)) ≫
        (baseUnitIso A).inv ≫ cupUnit (A := A) (G := G) := by
  sorry

/-- Transposing the cup gives precisely the tensor of the two negatively shifted arrows.
Source: paragraph (3) (blueprint: lem-sfb-internal-inflation-graded-cup).
Proof: expand cup as the lax tensor mate followed by coefficient multiplication. Apply
counit naturality at multiplication and the tensor-of-counits identity of
lem-sfb-monoidal-adjunction-mates and lem-sfb-monoidal-adjunction-unit-counit. Naturality
of the strong tensor comparison reduces the result to the tensor of the two transposes.
The shifted-tensor pullback calculus identifies the inflated shifted-unit comparison
with actionShiftedUnitTensor, with the same signed cochain conventions. -/
theorem inflationCupTranspose (p q : ℕ)
    (x : coefficient A G ⟶ (coefficient A G)⟦(p : ℤ)⟧)
    (y : coefficient A G ⟶ (coefficient A G)⟦(q : ℤ)⟧) :
    ((adjunction A G).homEquiv _ _).symm
        (inflationGradedCup A G p q (inflationPhi A G p x) (inflationPhi A G q y)) =
      (inflatedShiftedCoefficientIso A G (p + q)).hom ≫
        (actionShiftedUnitTensor A G p q).hom ≫
        (negativelyShiftedArrow A G p x ⊗ₘ negativelyShiftedArrow A G q y) ≫
        coefficientMultiply (A := A) (G := G) := by
  sorry

end ProfiniteGroup

/-- Universal normalized signs identify ordered cup with y[p] after x under Phi.
Source: paragraph (3), internal bar normalization, Stacks 0FNG
(blueprint: lem-sfb-internal-inflation-graded-cup).
Proof:
1. The action-topos presentation and the ringed derived tensor/comparison theorems give
   exact strong symmetric inflation with its signed cochain tensor, unit and shifts.
2. Exact-functor descent and Grothendieck K-injectives give the canonical invariant-
   inclusion derived adjunction, with its usual shift compatibility.
3. Monoidal adjunction mates make C = RΓ(A[0]) a unital cup algebra; its unit is the
   transpose of the identity under the fixed unit comparison (inflationPhiIdentity).
4. The tensor-of-counits mate identity transposes cup to the tensor of the two negative-
   source arrows f = x[-p] and g = y[-q], as in inflationCupTranspose.
5. Extract the second shift using kappa: Z tensor A[-q] → Z[-q]. Unitor naturality,
   without swapping f and g, gives m(f tensor g) = g f[-q] kappa. The shift-descent
   theorem makes this valid on arbitrary derived arrows, not just chain maps.
6. On the one nonzero total tensor summand of the shifted regular units, the integer-
   shift tensor theorem shows kappa followed by the fixed shifted-unit comparison is
   a sign times ordinary shift addition. This sign depends only on p,q and the fixed
   extraction order; every sign factor is a power of (-1)^(pq), so either zero degree
   gives +1. No coefficient, group or class enters this computation.
7. Shift back by p+q and use additivity of the adjunction bijection: g[p+q] is y[p]
   and f[-q][p+q] is x. Thus the order is y[p] after x. The zero ring makes all arrows
   zero without changing the universal integer sign; the trivial group gives the
   identity invariant-inclusion adjunction. These arguments cover all natural degrees.
-/
theorem internalInflationGradedCup :
    ∃ t : ℕ → ℕ → ℤ,
      (∀ p q : ℕ, t p q = 1 ∨ t p q = -1) ∧
      (∀ p : ℕ, t p 0 = 1) ∧ (∀ q : ℕ, t 0 q = 1) ∧
      ∀ (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
        [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
        (p q : ℕ) (x : coefficient A G ⟶ (coefficient A G)⟦(p : ℤ)⟧)
        (y : coefficient A G ⟶ (coefficient A G)⟦(q : ℤ)⟧),
      inflationGradedCup A G p q (inflationPhi A G p x) (inflationPhi A G q y) =
        t p q • inflationPhi A G (p + q)
          (ShiftedHom.comp x y (by simp [Nat.cast_add, add_comm])) := by
  sorry

end CategoryTheory.CondensedDerivedRestriction
