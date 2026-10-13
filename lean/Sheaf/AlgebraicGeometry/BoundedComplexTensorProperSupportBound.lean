/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # A proper support bound for tensor with a bounded complex

Source: Stacks Project, Tag 0DJQ, verification of the support hypothesis of 08EV;
Tags 01AT (support), 09MQ (4) and 03GN (descent along a proper surjection).
(blueprint: lem-pc-bounded-complex-tensor-proper-support-bound).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Tensoring any derived object with a bounded complex with proper termwise supports
puts all cohomology supports inside one closed subset proper over the base. No perfection,
coherence, relative flatness, Noetherian assumption or cohomology boundedness is needed.
This asserts containment; the cohomology supports need not themselves be closed.
Source: Stacks Project, Tag 0DJQ, support verification for 08EV; Tags 01AT, 09MQ (4), 03GN.

Proof:
1. If [c,d] bounds G, let Z be the union of the supports of G^n for c <= n <= d.
   Terms outside the interval are zero, with empty support. This is a finite union of
   closed subsets. If c > d the entire complex is zero and the union is empty.
2. Each reduced term support maps by a closed immersion into the reduced union Z.
   The finite disjoint union of these supports therefore maps properly and surjectively
   to Z. Its map to S is proper by the assumed properness of every term support.
   Separatedness of Z over S descends along this proper surjection (09MQ (4)), and
   universal closedness descends by 03GN. Local finite type follows from Z being a
   closed subscheme of X. These three properties make Z proper over S.
3. On the open complement of Z every term of G has zero stalks, hence is the zero sheaf.
   Therefore the restricted complex G is zero. Restriction to an open commutes with
   the K-flat derived tensor, and tensor with zero is zero, so E tensor^L G restricts
   to zero there, for arbitrary E. Exactness of open restriction shows every cohomology
   sheaf is zero on this complement. Its nonzero-stalk locus is consequently contained
   in Z, as asserted. For an empty Z the same proof gives zero cohomology everywhere.
(blueprint: lem-pc-bounded-complex-tensor-proper-support-bound). -/
theorem boundedComplex_tensor_proper_support_bound
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hGproper : ∀ n : ℤ, Modules.HasSupportProperOver f (G.X n)) :
    ∃ Z : TopologicalSpace.Closeds X, IsClosedSubsetProperOver f Z ∧
      ∀ i : ℤ,
        {x : X | ¬ Subsingleton
          ((Modules.presheaf (X := X)
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
                (E ⊗ DerivedCategory.Q.obj G))).stalk x)} ⊆ (Z : Set X) := by sorry

end AlgebraicGeometry.Scheme
