/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseFlat
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseKFlat

/-! # Flatness under sectionwise reindexing

Source: Stacks Project, Tags 03EL and 06YN; the tensor argument in Steps 4--5 of
`lem-pod-reindexing-hom-resolution-model`.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance 2000] SheafOfModules.hasSheafify_coefficientUniverse
attribute [local instance 2000] SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- Sectionwise inverse image, with an invertible coefficient identification, preserves
flat module sheaves and K-flat complexes.
Source: Stacks Project, Tags 03EL and 06YN; blueprint dual-Tate compatibility, Step 1
(blueprint: lem-pod-sectionwise-flat-kflat).

Proof: postcomposition by the scheme isomorphism is an equivalence of pro-etale sites.
Its reverse, with the inverse transported scalar action, gives an inverse module
functor G to the displayed functor F. Both functors are additive and exact, and
preserve all existing sums. Compare sheafified sectionwise tensor products by sending
a pure tensor a tensor b to the same tensor, with its scalar action transported by c.
The balanced relations match because c is a ring isomorphism. This gives a natural
isomorphism F(A tensor B) = FA tensor FB. For a flat module M and any exact sequence
on X, apply G, tensor with M, and apply F. The comparison identifies the resulting
exact sequence with the original sequence tensored with FM, proving flatness.
For complexes, in degree r use preservation of the direct sum over p+q=r and the
same tensor comparison. Naturality and additivity identify both differential terms,
including the sign (-1)^p, so this is an isomorphism of total tensor complexes.
If K is K-flat and C is acyclic on X, then GC is acyclic; hence GC tensor K is
acyclic. Applying F and the total comparison identifies it with C tensor FK,
which is therefore acyclic. This is precisely the independent-coefficient K-flat
predicate. The argument applies to arbitrary ring sheaves and unbounded complexes;
it uses no exactness of infinite products and no boundedness hypothesis. -/
theorem isoSectionwiseModuleInverseImage_flat_kFlat
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
    (∀ M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY),
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology Y) (R := RY) M →
        SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (J := ProEt.topology X) (R := RX) (F.obj M)) ∧
    (∀ K : CochainComplex (SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology Y) (R := RY) K →
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology X) (R := RX)
          ((F.mapHomologicalComplex (.up ℤ)).obj K)) := by
  refine ⟨?_, ?_⟩
  · exact isoSectionwiseModuleInverseImage_preservesFlat g RY RX c F _hF
  · exact isoSectionwiseModuleInverseImage_preservesKFlat g RY RX c F _hF

end AlgebraicGeometry.Scheme
