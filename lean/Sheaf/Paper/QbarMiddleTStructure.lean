/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Sheaf.Paper.IntrinsicQbarCategory
public import Sheaf.Paper.QbarPerverseSubcategories
public import Sheaf.SixFunctors.ArbitraryFieldVerdier
public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds
import Sheaf.Paper.PbcVerdierAxioms
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The middle perverse t-structure on intrinsic common-stage coefficients

Source: BBD, Sections 2.2.11--2.2.19 and 4.0; Bhatt--Scholze, Proposition 6.8.14
and Remark 6.8.15 (blueprint: lem-per-qbar-middle-tstructure).

The support and cosupport predicates are the recorded intrinsic adic predicates,
with the relative dualizing object given by the exceptional adjunction over the base field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Pretriangulated AlgebraicGeometry

namespace WeilConjectures

/-- Middle support and cosupport define a bounded t-structure, with its right-orthogonal
characterization and extension closure in every degree.
Source: BBD 1.3.4, 1.4.9--1.4.10, 2.2.11--2.2.19 and 4.0; Bhatt--Scholze 6.8.14--15
(blueprint: lem-per-qbar-middle-tstructure).
Proof: (1) The support inequalities and reversal of shifts by the relative Verdier dual
identify the shifted classes and give their shift inclusions. (2) Refine the constructible
nonzero-fibre loci by a complementary open and closed pair. Comparing closures of their
locally closed strata shows that support dimension is the maximum of its two restrictions.
Thus upper membership is detected by the two ordinary restrictions. (3) Apply this to
the dual: dual recollement identifies lower membership with open restriction and
extraordinary closed restriction. (4) For each finite collection of objects choose the
generic lisse open with lower-dimensional complement. On a component of dimension d,
upper and lower bounds are the ordinary bounds at n-d, by normalized generic duality.
Conservativity of geometric fibres assembles the disjoint components. (5) Induct on
dimension, starting with the empty scheme. Adjunction and the first localization triangle
reduce orthogonality to the generic ordinary bound and the smaller-dimensional complement.
Representable-Hom exactness supplies the vanishing on the whole scheme. (6) On the generic
open take ordinary truncations at -d. Take first the fibre of K to the direct image of its
upper truncation, then the fibre of the resulting object to the closed direct image of
its lower truncation on the complement. (7) The octahedron supplies the final truncation
triangle; the four recollement restriction identities verify its upper and lower bounds.
This proves the t-structure axioms by the same dimension induction. (8) Bounded ordinary
cohomology and finite dimension bound the support inequalities above; applying the same
argument to the bounded relative dual gives the lower bound. Enlarge the upper bound to
order the two indices. (9) Orthogonality gives one direction of the displayed equivalence.
For the converse, truncate at n-1; the assumed Hom vanishing and exactness force the lower
term to be zero, so K is isomorphic to its term in degree at least n. (10) Apply the general
t-structure extension-closure theorem to both classes at every index. -/
theorem qbar_middle_tstructure
    (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    ∃ t : Triangulated.TStructure (generalAlgebraicallyClosedConstructibleCategory l Ω X),
      (∀ n : ℤ, t.le n = QbarPerverseLE l X Ω n) ∧
      (∀ n : ℤ, t.ge n = QbarPerverseGE l X Ω k hl n) ∧
      (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
        ∃ m n : ℤ, m ≤ n ∧ t.le n K ∧ t.ge m K) ∧
      (∀ (n : ℤ) (K : generalAlgebraicallyClosedConstructibleCategory l Ω X),
        QbarPerverseGE l X Ω k hl n K ↔
          ∀ A : generalAlgebraicallyClosedConstructibleCategory l Ω X,
            QbarPerverseLE l X Ω (n - 1) A → ∀ f : A ⟶ K, f = 0) ∧
      (∀ (n : ℤ) (T : Triangle (generalAlgebraicallyClosedConstructibleCategory l Ω X)),
        T ∈ distTriang (generalAlgebraicallyClosedConstructibleCategory l Ω X) →
          (QbarPerverseLE l X Ω n T.obj₁ → QbarPerverseLE l X Ω n T.obj₃ →
            QbarPerverseLE l X Ω n T.obj₂) ∧
          (QbarPerverseGE l X Ω k hl n T.obj₁ → QbarPerverseGE l X Ω k hl n T.obj₃ →
            QbarPerverseGE l X Ω k hl n T.obj₂)) := by
  sorry

end WeilConjectures
