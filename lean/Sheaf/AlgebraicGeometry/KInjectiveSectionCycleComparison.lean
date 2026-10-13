/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sheaf.Paper.DerivedSectionsLeftExactBottom

/-! # Identifying section cohomology with the quotient of section cycles

Source: Stacks Project, Tags 0AVW and 08D4, canonical comparison calculation.
(blueprint: lem-sc-kinjective-section-cycle-comparison).
-/

@[expose] public section
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical quotient of section cycles computes the homology sheaf sections
when the derived lower truncation projection is invertible in degree n.
Source: Stacks Project, Tag 0AVW, omitted cohomology calculation, and Tag 08D4(1).
(blueprint: lem-sc-kinjective-section-cycle-comparison).

Proof: Put A = truncLE n I and B = truncGE n A. Since F preserves kernels,
H^n(F(A)) maps isomorphically to H^n(F(I)). The natural comparison F(I) to
RF(Q(I)) is invertible because I is K-injective: a comparison to a K-injective
resolution is a homotopy equivalence, which an additive functor preserves.
The upper-truncation map RF(Q(A)) to RF(Q(I)) is invertible on H^n by left
exactness. Naturality therefore makes the comparison for A invertible on H^n.
The hypothesis and naturality of lower truncation give invertibility on H^n
of RF(Q(A)) to RF(Q(B)): upper truncation leaves H^n of RF unchanged. The complex
B has just H^n(I) in degree n; left exactness identifies bottom derived
cohomology with F(H^n(I)), and this is the natural comparison for B.
In the naturality square for A to B, the degree-n map is the projection of
cycles to their homology class. Uniqueness of kernels identifies the cycles
of F(I) with F of the chosen cycles of I. Their boundaries are exactly the
image of F(h.f'). Thus their homology is the displayed cokernel, and uniqueness
of cokernel descent identifies the composite isomorphism with the displayed
map, since its composite with cokernel.pi is F(h.pi). This is an identity of
canonical maps, not a choice of an unrelated isomorphism. This works for the
zero complex, every integer degree, and any left exact additive F. -/
theorem kInjective_section_cycle_comparison
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (I : CochainComplex C ℤ) [I.IsKInjective] (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I))))) :
    IsIso (cokernel.desc (F.map (I.sc n).homologyData.left.f')
      (F.map (I.sc n).homologyData.left.π) (by
        rw [← F.map_comp, (I.sc n).homologyData.left.f'_π, F.map_zero])) := by sorry

end AlgebraicGeometry
