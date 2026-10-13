/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-! # Relative comparison triangles on a source-open union

Source: Stacks Project, Tags 0DJ9 and 08HZ, applied on the union.
(blueprint: lem-pc-single-complex-open-union-triangles).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
namespace AlgebraicGeometry

/-- The open comparisons on a union, its two members and their intersection
are the components of a morphism of distinguished relative Mayer--Vietoris
triangles. No comparison is assumed or asserted to be invertible.

Source: Stacks Project, Tag 0DJ9, induction diagram, and Tag 08HZ, functorial
relative Mayer--Vietoris; Tag 08HY, the canonical base-change map.
(blueprint: lem-pc-single-complex-open-union-triangles).

Proof: Put W = U union V. Compactness of the three opens and quasi-separatedness
of X make W -> X quasi-compact, hence W -> S qcqs. Restrict the square to W
and its cartesian inverse image W'. The inverse images of U and V cover W;
their intersection is the inverse image of U intersection V. Since g is affine,
its base change is affine, so all three opens in W' are quasi-compact as well.
Restrict the two coefficients by derived pullback and transport the coefficient
arrow using the canonical pullback composition isomorphisms. These restricted
coefficients have quasi-coherent cohomology.
Use K-injective representatives with injective terms to construct the functorial
relative Mayer--Vietoris triangles of Tag 08HZ on W and W'. Restriction to opens
preserves K-injectivity. In each degree sheaf gluing gives exactness at the first
two terms of the restriction sequence, and flasqueness of injective sheaves gives
surjectivity onto the overlap term. Thus the short exact sequences of complexes
give distinguished triangles. Apply Lg* to the triangle over S. Identify its
middle term with the biproduct using additivity.
Transpose the restricted coefficient arrow under the derived pullback adjunction,
use functoriality of these restriction sequences, and transpose back. Naturality
of the short-exact-sequence boundary gives the connecting square too. Identify
the resulting three components by the mates formula of Tag 08HY: expand the
composite adjunction counit and use the canonical pullback composition comparisons
and their associativity. The nested-open image isomorphisms identify the twice
restricted terms with the ambient open terms. Transport the triangles and their
morphism along these identifications. The components become precisely b_W,
b_U direct-sum b_V, and b_(U intersection V) in the statement.
Empty opens yield zero terms; repeated or contained opens yield the corresponding
split restriction sequences. Zero coefficients and arbitrary coefficient maps
are included; no invertibility or global cover of X is used. -/
theorem singleComplexOpenComparison_union_triangles
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (hUqc : IsCompact (U : Set X)) (hVqc : IsCompact (V : Set X))
    (hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X)) :
    let a : X.Opens → Arrow (schemeDerivedCategory S') := fun Z ↦
      Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)
    ∃ (d₁ : (a (U ⊔ V)).left ⟶ (a U).left ⊞ (a V).left)
      (d₂ : (a U).left ⊞ (a V).left ⟶ (a (U ⊓ V)).left)
      (d₃ : (a (U ⊓ V)).left ⟶ (a (U ⊔ V)).left⟦(1 : ℤ)⟧)
      (d₁' : (a (U ⊔ V)).right ⟶ (a U).right ⊞ (a V).right)
      (d₂' : (a U).right ⊞ (a V).right ⟶ (a (U ⊓ V)).right)
      (d₃' : (a (U ⊓ V)).right ⟶ (a (U ⊔ V)).right⟦(1 : ℤ)⟧),
      Triangle.mk d₁ d₂ d₃ ∈ distTriang (schemeDerivedCategory S') ∧
      Triangle.mk d₁' d₂' d₃' ∈ distTriang (schemeDerivedCategory S') ∧
      ∃ t : Triangle.mk d₁ d₂ d₃ ⟶ Triangle.mk d₁' d₂' d₃',
        t.hom₁ = (a (U ⊔ V)).hom ∧
        t.hom₂ = biprod.map (a U).hom (a V).hom ∧
        t.hom₃ = (a (U ⊓ V)).hom := by sorry

end AlgebraicGeometry
