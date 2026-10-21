/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

/-! # K-flat tensor with a module in degree zero on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tag 06YU, definition-derived-tor and
its preceding construction, specialized to a degree-zero second factor.
(blueprint: lem-sf-ringed-kflat-single-tensor-comparison)

The tensor and its representative comparison are the published site-descent construction.
The termwise tensor is the existing tensor functor applied to a cochain complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{w} (Modules R)]

/-- The canonical comparison with termwise tensor, natural in both inputs and uniquely
normalized by every pair of flat-term K-flat resolutions. In the termwise functor the
objects, differentials and map components are respectively `P.X q tensor M`,
`P.d q q' tensor id`, and `u.f q tensor f`. The single-complex total identification is
`CochainComplex.mapBifunctorSingle₂Iso`, whose sole nonzero summand is `(q,0)`.
No boundedness, termwise flatness of P, or flatness of M is assumed.

Source: Stacks Project, Tag 06YU, definition-derived-tor and preceding construction
(blueprint: lem-sf-ringed-kflat-single-tensor-comparison).

Proof plan (the node's seven steps):
1. Work on a coefficient-universe small model of the site (def-weil-size-convention).
   Module sheaves are Grothendieck abelian (prop-pur-kinjective-resolutions-exist),
   their tensor is closed symmetric and additive (lem-pc-sheaf-modules-tensor-closed),
   and they have functorial flat resolutions (lem-trf-site-functorial-flat-resolution).
2. The acyclic-tensor K-flat predicate implies preservation of quasi-isomorphisms
   (lem-pur-kflat-tensor-quasiiso-independent). The signed swap on bidegree (i,j)
   has sign (-1)^(ij); its two differential coefficients are (-1)^(ij) and
   (-1)^(ij+j). It gives preservation in the other variable. Conversely test 0 to X
   for acyclic X. Thus it agrees with def-sfb-preserves-kflat-quasi-iso.
3. Apply lem-sfb-derived-monoidal. Its natural localization multiplication is invertible
   whenever one argument is K-flat, including the identity resolution of P.
4. Identify that tensor with the specified site-descent tensor by extending the
   comparison on flat-term K-flat pairs, and its inverse, uniquely
   (lem-weil-pbc-site-derived-tensor-descent). The resulting multiplication m has
   normalization m = representativeIso.inv on those pairs.
5. In total tensor with M[0], all summands except (q,0) vanish. Projection and
   inclusion give delta = mapBifunctorSingle₂Iso; the second differential vanishes,
   so the first is d_P tensor id. Compose m with Q(delta) to obtain c.
6. Naturality of m and delta gives precisely the displayed square, whose right edge
   is Q of the termwise tensor map. In degree q this map is u.f q tensor f.
7. For any flat-term K-flat resolutions p and b (lem-pc-kflat-resolution), naturality
   gives beta followed by tensor(Qp,Qb) followed by c = Q(total(p,b) followed by delta).
   The first two arrows are invertible. Thus this equation uniquely determines c,
   proves independence of both resolutions, and gives uniqueness of the whole family.
-/
theorem ringed_kFlat_single_tensor_comparison :
    ∃! c : ∀ (P : CochainComplex (Modules R) ℤ)
        (_ : CochainComplex.IsKFlatIndependentCoefficients P) (M : Modules R),
      ((derivedTensor R).obj (DerivedCategory.Q.obj P)).obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≅
        DerivedCategory.Q.obj
          ((((ordinaryTensor R).flip.obj M).mapHomologicalComplex (.up ℤ)).obj P),
      (∀ (P P' : CochainComplex (Modules R) ℤ)
          (hP : CochainComplex.IsKFlatIndependentCoefficients P)
          (hP' : CochainComplex.IsKFlatIndependentCoefficients P')
          (M M' : Modules R) (u : P ⟶ P') (f : M ⟶ M'),
        ((derivedTensor R).map (DerivedCategory.Q.map u)).app _ ≫
            ((derivedTensor R).obj (DerivedCategory.Q.obj P')).map
              (DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map f)) ≫
            (c P' hP' M').hom =
          (c P hP M).hom ≫ DerivedCategory.Q.map
            (((((ordinaryTensor R).flip.obj M).mapHomologicalComplex (.up ℤ)).map u) ≫
              (NatTrans.mapHomologicalComplex ((ordinaryTensor R).flip.map f) (.up ℤ)).app P')) ∧
      (∀ (P : CochainComplex (Modules R) ℤ)
          (hP : CochainComplex.IsKFlatIndependentCoefficients P) (M : Modules R)
          (A B : CochainComplex (Modules R) ℤ)
          (hA : CochainComplex.IsKFlatIndependentCoefficients A)
          (hB : CochainComplex.IsKFlatIndependentCoefficients B)
          (hAf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (A.X n))
          (hBf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (B.X n))
          (p : A ⟶ P) (b : B ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj M),
        QuasiIso p → QuasiIso b →
          (representativeIso R A B hA hB hAf hBf).hom ≫
              ((derivedTensor R).map (DerivedCategory.Q.map p)).app _ ≫
              ((derivedTensor R).obj (DerivedCategory.Q.obj P)).map
                (DerivedCategory.Q.map b) ≫ (c P hP M).hom =
            DerivedCategory.Q.map
              (((totalTensor R).map p).app B ≫ ((totalTensor R).obj P).map b ≫
                (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M P).hom)) := by
  sorry

end SheafOfModules
