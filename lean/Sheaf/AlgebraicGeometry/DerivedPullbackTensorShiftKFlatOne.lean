/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Exact comparisons on K-flat representatives for translation by one

Source: Stacks Project, Tag 08EU, proof, and Cohomology, equation (20.54.2.1).
(blueprint: lem-sc-derived-pullback-tensor-shift-kflat-one).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- The geometric construction only needs its compatibility squares on K-flat
representatives and for translation by one. No compatibility for arbitrary derived
objects or for other integer translations is asserted here.
Source: Stacks Project, Tag 08EU, exactness assertion in the proof, and Cohomology,
equation (20.54.2.1).
(blueprint: lem-sc-derived-pullback-tensor-shift-kflat-one).

Proof: form total tensor products on K-flat resolutions. The Koszul comparison
between translation of the varying first complex and translation of its tensor
product preserves the standard mapping-cone triangles. Its zero and addition
identities give coherent shift structures after localization. Apply termwise
module pullback to K-flat resolutions: it preserves mapping cones, so its descended
shift structure is exact. Choose this comparison jointly with the tensor comparisons
for the supplied strong monoidal structure, using tensor with the translated unit.
The inverse tensorator and the unit isomorphism identify pullback of this expression
with the analogous expression on the target. The associativity and unit equations
of that supplied structure give the coherent zero and addition equations.
For a K-flat varying complex, compute the square for translation by one: the two
paths identify the same translated tensor product, with the same Koszul sign.
Naturality of the tensor comparison in the fixed factor gives the first displayed
square, and associativity of the supplied tensorator gives the second. Transport
mapping-cone triangles along these comparisons to obtain the three exactness
clauses. All equations descend through localization because comparison maps
respect quasi-isomorphisms. This is the representative calculation only: extending
these squares along K-flat replacement isomorphisms and to all integer translations
is done separately. The zero complex and empty schemes give zero squares; degree
zero shifts are controlled by the unit equation, rather than division by a sign. -/
theorem derivedPullback_tensorShift_kFlat_one
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sF : (derivedPullback f).CommShift ℤ)
      (sY : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ)
      (sZ : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ),
      letI := sF
      letI := sY
      letI := sZ
      (derivedPullback f).IsTriangulated ∧
      (∀ M : schemeDerivedCategory Y, (tensorRight M).IsTriangulated) ∧
      (∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated) ∧
      (∀ {M N : schemeDerivedCategory Z} (b : M ⟶ N)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Z.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((curriedTensor (schemeDerivedCategory Z)).flip.map b)
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app K ≫ (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫ ((tensorRight N).commShiftIso (1 : ℤ)).hom.app K) ∧
      (∀ (M : schemeDerivedCategory Y)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((Functor.flipping.functor.map
          (Functor.OplaxMonoidal.δNatTrans (derivedPullback f))).app M)
        ((tensorRight M ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫
            ((derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M)).commShiftIso
              (1 : ℤ)).hom.app K) := by sorry

end AlgebraicGeometry
