/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.CategoryTheory.CanonicalResolutionDerivedIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! # Resolution comparisons and the composite derived unit

Source: Stacks Project, derived.tex, Tags 015M and 015N.
(blueprint: lem-pc-grothendieck-resolution-unit-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Homology of the canonical comparison computes the prescribed resolution comparison.
Source: Stacks Project, Tag 015M, resolution computation of derived functors.
(blueprint: lem-pc-canonical-resolution-homology-comparison).

Proof: For the chosen injective resolution, expand the single-object homology comparison;
its final inverse resolution comparison cancels the resolution comparison in the left
side. For the prescribed resolution, choose a comparison lifting the identity of X.
Its extension induces a homotopy equivalence, and naturality of the derived unit shows
that the chosen derived comparison followed by its image is resolutionDerivedIso F I.
Naturality of homologyFunctorObjQIso and isoRightDerivedObjCochainComplex identifies
its map on homology with the prescribed resolution comparison. Finally expand
isoRightDerivedObjCochainComplex: its inverse map/extension homology comparison cancels
the map/extension factor in canonicalResolutionDerivedIso, and its inverse extension
homology comparison cancels the last factor on the right. This works also for n = 0.
-/
theorem resolution_homology_transport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [EnoughInjectives A] {B : Type uB} [Category.{vB} B]
    [Abelian B] [HasDerivedCategory A]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    (X : A) (I : InjectiveResolution X) (n : ℕ) :
    (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫
          (I.isoRightDerivedObj F n).hom =
        (DerivedCategory.Plus.homologyFunctor B n).map (canonicalResolutionDerivedIso F I).hom ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso
            ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
              ComplexShape.embeddingUpNat, 0, inferInstance⟩ n).hom ≫
          (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom := by sorry

end CategoryTheory
