/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

/-!
# Exact comparison and the hypercohomology left edge

Source: Stacks Project, Derived Categories, Tag 015J, functoriality of the truncation
spectral object; the canonical derived base-change unit equation.
(blueprint: lem-pur-hypercohomology-edge-exact-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uB vB uB' vB' uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [IsGrothendieckAbelian.{vB} B] [HasDerivedCategory.{vB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B']
  [IsGrothendieckAbelian.{vB'} B'] [HasDerivedCategory.{vB'} B']
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [IsGrothendieckAbelian.{vC} C] [HasDerivedCategory.{vC} C]
  (G : B ⥤ C) (G' : B' ⥤ C) (β : B ⥤ B')
  [G.Additive] [G'.Additive] [β.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteLimits G']
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]

/-- Remove the derived identity from the canonical derived comparison.
Source: the unit definition of derived base change
(blueprint: lem-pur-hypercohomology-edge-exact-comparison). -/
abbrev normalizedDerivedBaseChange (e : G ⋙ 𝟭 C ⟶ β ⋙ G') :
    G.rightDerivedFunctorPlus ⟶ β.mapDerivedCategoryPlus ⋙ G'.rightDerivedFunctorPlus :=
  G.rightDerivedFunctorPlus.rightUnitor.inv ≫
    whiskerLeft G.rightDerivedFunctorPlus (mapDerivedCategoryPlusIdIso C).inv ≫
    rightDerivedFunctorPlusBaseChange e

/-- Exact comparison preserves the canonical normalized hypercohomology left edge.
Source: functoriality of the truncation spectral object and the derived base-change
unit equation (blueprint: lem-pur-hypercohomology-edge-exact-comparison).

Proof:
1. Write τ for the normalized derived comparison. It commutes with shifts: the
canonical derived-identity isomorphism does so after restriction to the bounded-below
homotopy category, and `rightDerivedFunctorPlusBaseChange` commutes with shifts by
its unit characterization. The comparison of truncation spectral objects is the
composite of `τ.mapTriangulatedSpectralObject`, the functor-composition comparison,
and the image under RG' of `β.mapTriangulatedSpectralObjectObjIso`.
2. Apply `Abelian.SpectralObject.leftEdge_naturality`. On the interval from bottom
to top its component is H^q(τ_K), because both extended truncations are identities.
3. On the interval [q,q+1), identify each truncation with H^q(K)[-q]. The identity
`mapDerivedCategoryPlus_eTruncGELTIsoApp_eTruncLTCompETruncGEIso`, with ψ the identity,
identifies the β-truncation comparison with β applied to the single-degree
identification, followed by β's shift comparison, its single-functor comparison,
and the single functor applied to its homology comparison.
4. Naturality of τ moves the single-degree identification past τ. Its shift
compatibility and homology-shift naturality reduce the remaining comparison to
an object in degree zero. Apply `rightDerivedBaseChange_zero_unit`: cancel the
invertible degree-zero unit of G, and use the canonical single/derived homology
isomorphisms. This gives e at H^q(K), followed by G' of β's homology comparison.
Substitute this target component in Step 2 and associate the composites. -/
theorem hypercohomologyLeftEdge_exactComparison (e : G ⋙ 𝟭 C ⟶ β ⋙ G')
    (K : DerivedCategory.Plus B) [K.IsGE 0]
    [(β.mapDerivedCategoryPlus.obj K).IsGE 0] (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor C q).map
        ((normalizedDerivedBaseChange G G' β e).app K) ≫
      (G'.hypercohomologySpectralObjectFunctor.obj (β.mapDerivedCategoryPlus.obj K)).leftEdge q ≫
      (G'.hypercohomologyLeftEdgeTargetIso q).hom.app (β.mapDerivedCategoryPlus.obj K) =
    (G.hypercohomologySpectralObjectFunctor.obj K).leftEdge q ≫
      (G.hypercohomologyLeftEdgeTargetIso q).hom.app K ≫
      e.app ((DerivedCategory.Plus.homologyFunctor B q).obj K) ≫
      G'.map ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K) := by sorry

end CategoryTheory.Functor
