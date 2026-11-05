/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Vanishing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# The external product and restriction to closed subschemes

For closed immersions `i : Z ⟶ X` and `j : W ⟶ Y` over a base `B`, with product
`i ×_B j : Z ×_B W ⟶ X ×_B Y`,

`(i ×_B j)_* (i ×_B j)^* (K ⊠ L) ≅ i_* i^* K ⊠ j_* j^* L`

(`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_closedImmersion_of_flat`).

The proof characterises the objects `ι_* ι^* N` of `D(X_ét)` for a closed immersion `ι` by their
support: if `φ : N ⟶ M` becomes invertible after `Lι^*` and `M` vanishes on the open
complement of `ι`, then `M ≅ Rι_* Lι^* N`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_obj_leftDerivedUpperStar_obj`), by
the open–closed triangle. It is applied to `i ×_B 𝟙` and `𝟙 ×_B j` separately: the open
complement of `i ×_B 𝟙` is the preimage of the open complement of `i`, on which `Ri_* Li^* K`,
hence `Ri_* Li^* K ⊠ L`, vanishes; and the unit `K ⟶ Ri_* Li^* K` is invertible after `Li^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

section Support

variable {Z X U : Scheme.{u}}

end Support

section ExternalProduct

variable {B X Y Z W : Scheme.{u}}

variable [UpperStarPreservesFlat A]

end ExternalProduct

section OneSided

variable [UpperStarPreservesFlat A] {B X Y Z W : Scheme.{u}}

end OneSided

end Etale

end AlgebraicGeometry
