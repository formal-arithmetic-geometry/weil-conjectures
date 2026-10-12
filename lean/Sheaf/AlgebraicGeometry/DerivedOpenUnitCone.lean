/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionQCoh

/-! # Support and quasi-coherence of the derived open-unit cone
Source: Stacks Project, Tag 09IR, proof of lemma-orthogonal-koszul-complex;
Tag 08D5, quasi-coherence of derived direct image.
(blueprint: lem-pc-derived-open-unit-cone).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

/-- The cone of the open restriction unit has quasi-coherent cohomology and vanishes
on the open. This assertion has no Koszul or orthogonality hypothesis.
Source: Stacks Project, Tag 09IR, proof of lemma-orthogonal-koszul-complex;
Tag 08D5, preservation of quasi-coherent cohomology by qcqs direct image.
(blueprint: lem-pc-derived-open-unit-cone).

Proof: Identify the over-site module category with modules on the open subscheme.
The open inclusion is quasi-compact since U is compact in the affine scheme; it is
separated. Restriction is exact and preserves quasi-coherent sheaves. Its derived
right adjoint is the derived direct image, by uniqueness of right adjoints, hence
preserves quasi-coherent cohomology by Tag 08D5. Thus both first terms of the triangle
have quasi-coherent cohomology. The long exact cohomology sequence and closure of
quasi-coherent sheaves under kernels, cokernels and extensions give the same for C.
The derived counit of an open inclusion is invertible: restrict a K-injective
resolution of the direct image to U and evaluate on an open W in U, where its sections
are exactly the sections of the original resolution on W. The adjunction triangle
identity makes restriction of the unit invertible. Exact restriction sends the given
triangle to a distinguished triangle with invertible first arrow, so its third object
is zero. Uniqueness of right adjoints transports both assertions to the supplied R
and adjunction, without choosing an arbitrary object from an existence statement.
The empty open and the entire spectrum satisfy the same argument. -/
theorem derived_open_unit_cone_properties
    (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens)
    (hqc : IsCompact (U : Set (Spec (.of A))))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ⥤
      schemeDerivedCategory (Spec (.of A)))
    (adj : (SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory ⊣ R)
    (E : schemeDerivedCategory (Spec (.of A)))
    (hE : schemeDerivedQCohProperty (Spec (.of A)) E)
    (C : schemeDerivedCategory (Spec (.of A)))
    (g : R.obj ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj E) ⟶ C)
    (h : C ⟶ E⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (adj.unit.app E) g h ∈ distTriang _) :
    schemeDerivedQCohProperty (Spec (.of A)) C ∧
      IsZero ((SheafOfModules.overFunctor.{u}
        (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj C) := by sorry

end AlgebraicGeometry
