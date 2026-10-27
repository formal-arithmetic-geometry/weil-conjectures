/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

/-! # Flatness under sectionwise reindexing

Source: Stacks Project, Tags 03EL and 06YN; the flatness part of
`lem-pod-sectionwise-flat-kflat`.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance 2000] SheafOfModules.hasSheafify_coefficientUniverse
attribute [local instance 2000] SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- Sectionwise inverse image with an invertible coefficient identification preserves
flat module sheaves.

Source: Stacks Project, Tag 03EL and the flatness part of the tensor argument in
`lem-pod-sectionwise-flat-kflat` (blueprint: lem-pod-sectionwise-flat-kflat-flat).

Proof: postcomposition by the scheme isomorphism is an equivalence of pro-etale
sites. Reindex modules and transport the scalar action through the coefficient
isomorphism. The inverse reindexing functor is exact and the sectionwise tensor
comparison identifies tensoring after transport with transport after tensoring.
Applying the inverse to an exact sequence and using flatness, then transporting
back, proves exactness of tensoring with the image module. -/
theorem isoSectionwiseModuleInverseImage_preservesFlat
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (isoSectionwiseInverseImage g CommRingCat.{u + 1}).obj RY ≅ RX)
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY) ⥤
      SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)) [F.Additive]
    (_hF : F = isoSectionwiseModuleInverseImage.{u, u} g
      (RY := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)
      (RX := (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom) :
    ∀ M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY),
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology Y) (R := RY) M →
        SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (J := ProEt.topology X) (R := RX) (F.obj M) := by
  sorry

end AlgebraicGeometry.Scheme
