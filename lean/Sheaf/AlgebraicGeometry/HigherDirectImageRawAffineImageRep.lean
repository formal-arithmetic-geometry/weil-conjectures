/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
import Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit
import Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

/-! # Affine raw classes in the image of a stage

Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: sbc-lem-higher-image-raw-affine-image-rep).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- A raw cohomology class on an affine etale object has the same associated
higher-image section as a raw class at one stage. This says nothing about arbitrary
higher-image sections, sheaf colimits, or the injectivity of the comparison.
Source: Stacks Project, Tag 09Z1, the cohomology colimit in the proof; Tag 0EZM.
(blueprint: sbc-lem-higher-image-raw-affine-image-rep).

Proof: Replace the filtered opposite index by a small directed final poset.
Its opposite is initial, so the reindexed underlying scheme cone is limiting.
Base change it along the affine etale object U over S. The stages are qcqs:
their maps to U are base changes of the qcqs composite structure maps to S.
Their transitions are affine, and their limit is the pullback of the given limit.
The coefficient sheaves are all inverse images of G. Composition of inverse
images identifies their pullbacks to the limit with the fixed limit coefficient
sheaf, with identity transitions. Its colimit is that sheaf because the filtered
index is nonempty and connected. Put the coefficients in single complexes in
degree zero, with common lower bound zero. Compute their underlying abelian
cohomology by injective module resolutions, whose terms are acyclic for abelian
sections (03FD), and apply complex continuity 0EZM. Thus the raw class over U
comes from a raw class at a stage. Derived adjunction identifies the cohomology
pullback with the transition defined by its unit and counit. Naturality of the
unit, the triangle identity, and inverse-image composition identify the maps
from these raw classes to higher-image sections with higherDirectImageOverMap.
This gives the displayed equality. In negative degrees raw cohomology vanishes,
so choose any stage and the zero class; the filtered index is nonempty. -/
theorem exists_higher_image_raw_affine_image_rep
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left]
    (z : (higherDirectImagePresheaf Λ (c.pt.hom ≫ k) q
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G))).obj (op U)) :
    ∃ (i : I)
      (t : (higherDirectImagePresheaf Λ ((D.obj i).hom ≫ k) q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))).obj (op U)),
      ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op U))
        ((higherDirectImagePresheafToSheaf Λ ((D.obj i).hom ≫ k) q
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))).app (op U) t) =
      (higherDirectImagePresheafToSheaf Λ (c.pt.hom ≫ k) q
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G))).app (op U) z := by sorry

end AlgebraicGeometry.Etale
