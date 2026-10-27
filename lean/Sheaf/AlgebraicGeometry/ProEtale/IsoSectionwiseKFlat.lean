/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # K-flatness under sectionwise reindexing

Source: Stacks Project, Tag 06YN; the K-flatness part of
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
K-flat complexes for the independent-coefficient tensor predicate.

Source: Stacks Project, Tag 06YN and the K-flatness part of the tensor argument in
`lem-pod-sectionwise-flat-kflat` (blueprint: lem-pod-sectionwise-flat-kflat-kflat).

Proof: the inverse reindexing functor is an exact equivalence and preserves the
colimits forming total tensor complexes. The sectionwise tensor comparison is
natural in both variables and respects the signed differential. For an acyclic
complex on the target site, transport it by the inverse, apply K-flatness, and
transport the resulting acyclic total tensor complex back. -/
theorem isoSectionwiseModuleInverseImage_preservesKFlat
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
    ∀ K : CochainComplex (SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology Y) (R := RY) K →
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology X) (R := RX)
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
