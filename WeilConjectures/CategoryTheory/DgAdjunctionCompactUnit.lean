/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DgAlgebraDerivedCategory
public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

import WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts
import WeilConjectures.CategoryTheory.ShiftSaturatedIsoLocus
import WeilConjectures.CategoryTheory.LocalizingHomTest

/-!
# A compact regular-module image propagates the adjunction unit

Source: Stacks Project, dga.tex, Tag 09LZ, lemma-fully-faithful-in-compact-case,
in its abstract exact-adjunction form (blueprint: lem-sfb-dg-adjunction-compact-unit).
The dg source is the actual localization defined by `DgAlgebra.Derived`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DgAlgebra

/-- Compactness of the image of the regular dg module and invertibility of the unit
there imply invertibility everywhere and bijectivity of every map on Hom sets.
Source: Stacks Project, dga.tex, Tag 09LZ, with Tag 0FQE
(blueprint: lem-sfb-dg-adjunction-compact-unit).

Proof plan, following the five steps of the node:
1. By lem-sfb-dg-free-shift-derived-hom, Hom(A[n],M)=H^(-n)(M), naturally on
coprojections. Dg direct sums compute coproducts by lem-sfb-dg-sequential-colimit-triangle.
Cohomology commutes with direct sums, so A[n] is compact; exactness of T and
compactness of T(A) make T(A[n]) compact as well.
2. Lem-sfb-dg-property-p-devissage identifies the localizing closure of the shifts
of A with the entire dg derived category. Lem-sf-localizing-hom-test then says
that Hom from these shifts detects isomorphisms.
3. Lem-sc-compact-tests-right-adjoint-coproducts, applied to that compact detecting
family and its compact images, implies preservation of coproducts by R.
4. The unit isomorphism locus saturated under all shifts is replete and closed
under coproducts and triangles by lem-sc-shift-saturated-iso-locus. Shift compatibility
of the adjunction and the unit hypothesis put every A[n] in this locus.
Apply lem-sfb-dg-property-p-devissage and then take shift zero.
5. Adjunction followed by composition with the inverse unit at N identifies
Hom(T(M),T(N)) with Hom(M,N). Naturality makes this bijection inverse to T.map.
No generation of the target by T(A) is used. -/
theorem adjunction_unit_isIso_of_compact_regular
    (A : Algebra.{u}) [DerivedStructure A]
    {C : Type v} [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] [HasCoproducts.{u} C]
    (T : Derived A ⥤ C) (R : C ⥤ Derived A)
    [T.CommShift ℤ] [R.CommShift ℤ] [T.IsTriangulated] [R.IsTriangulated]
    (adj : T ⊣ R) [adj.CommShift ℤ]
    (hcoproducts : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) T)
    (hcompact : IsCompactObject.{u} (T.obj ((Q A).obj (regular A))))
    (hunit : IsIso (adj.unit.app ((Q A).obj (regular A)))) :
    (∀ M : Derived A, IsIso (adj.unit.app M)) ∧
      ∀ M N : Derived A, Function.Bijective (T.map : (M ⟶ N) → (T.obj M ⟶ T.obj N)) := by
  sorry

end CategoryTheory.DgAlgebra
