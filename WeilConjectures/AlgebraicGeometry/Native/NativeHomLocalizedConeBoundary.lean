/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSignedShiftLaws
import WeilConjectures.AlgebraicGeometry.Native.NativeHomLocalizedConeBoundaryTransport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # The signed native Hom boundary on localized cone triangles

Source: Stacks Project, Tags 08J9 and 08JC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

/-- On a localized ordinary cone triangle the specified signed boundary makes
contravariant native Hom into a distinguished triangle.
Source: Stacks Project, Tag 08JC, the cone calculation in lemma-RHom-triangulated
(blueprint: lem-sf-native-hom-localized-cone-boundary).

Proof: represent M by a K-injective complex I. Use the native Hom model U,
whose differential at product index p is (-1)^p times postcomposition by d_I
minus precomposition by the source differential. For Cone(f)^p=G^p ⊕ E^(p+1),
write its two restrictions as x_p and a_p. The signed bifunctor cone
isomorphism sends these to (y,x) in Cone(U(f))[-1], with
 y_j=(-1)^(j-1)*a_(j-1); its inverse has a_p=(-1)^p*y_(p+1).
In these coordinates the differential is (-d*y-U(f)*x,d*x), and restriction
to G is projection to x. Thus the first two triangle squares agree with the
inverse rotation of the cone triangle of U(f).
For the third square, transpose the displayed parameter-shift mate under
total-tensor evaluation. The raw mate at -1 reindexes the source product factor p to p-1 with
coefficient (-1)^(p-1): the argument tensor shift crosses the source degree
p-1. Multiplication by (-1)^q(1)=-1 changes this to (-1)^p, exactly the inverse
of the ordinary signed Hom shift at -1. Equivalently, for a split sequence
with connecting cochain h_p, the reversed Hom connecting map at the factor
C^p -> I^(p+n+1) is (-1)^(p+1) times precomposition by h_p. Expanding the
opposite third arrow followed by the corrected mate gives the same coefficient.
Composing with the cone comparison therefore leaves the inclusion of y.
This identifies the actual third arrow written
below, rather than an unspecified completion. Apply Q and the natural,
evaluation-characterized qhInternalHomToIhom isomorphisms for I. Hom into a
K-injective complex inverts quasi-isomorphisms. Transport along Q(I) ≅ M,
using naturality of the mate in its coefficient. The mapping cocone triangle
is distinguished, so the displayed triangle is distinguished as well. This
uses only ordinary cones; no assertion about arbitrary distinguished input
triangles is assumed. -/
theorem nativeHom_localized_cone_boundary
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {E G : CochainComplex C ℤ} (f : E ⟶ G) (M : DerivedCategory C) :
    let H := MonoidalClosed.internalHom.flip.obj M
    let T := (triangleOpEquivalence (DerivedCategory C)).functor.obj
      (op (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))
    Triangle.mk (H.map T.mor₁) (H.map T.mor₂)
      (H.map T.mor₃ ≫ siteHomSignedSourceComponent M 1 T.obj₁) ∈
        distTriang (DerivedCategory C) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  let M₀ := DerivedCategory.Q.obj I
  let H₀ := MonoidalClosed.internalHom.flip.obj M₀
  let H := MonoidalClosed.internalHom.flip.obj M
  let T := (triangleOpEquivalence (DerivedCategory C)).functor.obj
    (op (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))
  have hmodel :
      Triangle.mk (H₀.map T.mor₁) (H₀.map T.mor₂)
          (H₀.map T.mor₃ ≫ siteHomSignedSourceComponent M₀ 1 T.obj₁) ∈
        distTriang (DerivedCategory C) :=
    nativeHom_localized_cone_boundary_model f I
  obtain ⟨eT⟩ := nativeHom_localized_cone_boundary_transport f I M e.symm
  exact Pretriangulated.isomorphic_distinguished _ hmodel _ eT.symm

end AlgebraicGeometry.ProEtale
