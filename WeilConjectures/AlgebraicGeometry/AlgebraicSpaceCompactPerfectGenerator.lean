/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.CompactObject

/-! # A compact perfect generator on a quasi-compact quasi-separated algebraic space

Source: Stacks Project, Derived Categories of Spaces, Tags 09IY and 09M8
(blueprint: lem-sfb-space-compact-perfect-generator).

The derived category uses the recorded small affine ringed model, equivalent to the
original small etale module topos. Quasi-separatedness is absolute: the fibre product
of any two affine schemes mapping to X is quasi-compact (Properties of Spaces, 0AHR).
Coproduct existence is included in the conclusion, rather than assumed of D_QCoh.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is one perfect compact object detecting zero by all its integer shifts.
Source: Stacks Project, Derived Categories of Spaces, Tag 09IY,
`theorem-bondal-van-den-Bergh`, and Tag 09M8, `proposition-compact-is-perfect`
(blueprint: lem-sfb-space-compact-perfect-generator).

Proof:
1. Apply lem-sfb-space-perfect-weak-generator (09IY) to the given qcqs space.
   It gives a perfect P with quasi-coherent cohomology and the displayed zero-detection
   criterion for every E with quasi-coherent cohomology. Keep this same P.
2. Apply lem-sfb-space-perfect-objects-compact (09M8, perfect-to-compact direction)
   to P. Its hypotheses are precisely quasi-compactness and absolute quasi-separatedness.
   The category D_QCoh has small coproducts, computed by derived direct sums, and the
   canonical Hom-to-coproduct map for P is bijective for every small family.
3. D_QCoh is full in the ambient derived category, so its Hom groups and those used
   in the zero-detection criterion agree. The recorded small ringed-model equivalence
   preserves cohomology, coproducts, finite free summands and zero objects. Thus these
   are the same statements on the original small etale ringed topos. -/
theorem exists_compact_perfect_generator
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b))) :
    ∃ (hcoprod : HasCoproducts.{u} X.DerivedQCoh) (P : X.DerivedQCoh),
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
        X.smallStructureSheaf P.obj ∧
      @IsCompactObject.{u} X.DerivedQCoh _ _ hcoprod P ∧
      ∀ E : X.DerivedQCoh, IsZero E.obj ↔
        ∀ n : ℤ, Subsingleton (P.obj⟦n⟧ ⟶ E.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
