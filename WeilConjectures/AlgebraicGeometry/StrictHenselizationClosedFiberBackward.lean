/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality

/-!
# The closed point of a strict henselization

The closed point of an affine presentation of the strict henselization at a geometric point maps
to the image of that geometric point.

## References

* [Stacks Project, Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks Project, Tag 04GP](https://stacks.math.columbia.edu/tag/04GP)
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
/-- The closed point of an affine presentation of a strict henselization maps to the
selected geometric point. -/
theorem strictHenselizationStructuralMap_closedPoint_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictLocalization s) :
    (e.hom ≫ strictLocalizationToBase s) (IsLocalRing.closedPoint A) =
      s (IsLocalRing.closedPoint Ω) := by
  let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨hlocal, _, hbase, _⟩ := AlgebraicGeometry.strictHenselizationResidue s rfl
  let := hlocal
  have hforward := IsLocalRing.specializes_closedPoint
    (e.hom (IsLocalRing.closedPoint A))
  have hbackward := (IsLocalRing.specializes_closedPoint
    (e.inv (IsLocalRing.closedPoint (strictHenselization s)))).map e.hom.continuous
  have hpoint : e.hom (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (strictHenselization s) := by
    apply (hforward.antisymm ?_).eq
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id] at hbackward
    exact hbackward
  simpa only [Scheme.Hom.comp_apply, hpoint] using hbase
end AlgebraicGeometry.Scheme
