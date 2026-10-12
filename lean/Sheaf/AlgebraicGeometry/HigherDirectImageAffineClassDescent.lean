/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit
import Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
import Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Descent of affine higher-image sections

Source: Stacks Project, Tags 09Z1, 03Q8 and 0738.
(blueprint: sbc-lem-higher-image-affine-class-descent).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Every section of the limit higher image on an affine etale object descends.
Source: Stacks Project, Tag 09Z1, proof; Tag 0738(4).
(blueprint: sbc-lem-higher-image-affine-class-descent).

Proof:
1. Use a small directed final presentation of the filtered opposite index.
   Opposite initiality preserves the scheme limit. Pull back the inverse system
   to affine etale objects over S: its stages are qcqs, its transitions affine,
   and its limit is the pullback of c.pt. Composition of inverse images identifies
   the limit coefficient diagram with a constant diagram with value the pullback
   of G. Its colimit is that value because the index is nonempty and connected.
2. An injective module resolution is acyclic for underlying abelian sections
   (03FD), so the abelian continuity theorem applies after forgetting scalars,
   without a flatness assumption on the ring. Place the sheaves in degree zero
   and apply complex continuity (0EZM) to the systems from step 1. This identifies
   the cohomology-presheaf colimit comparison on the affine basis. Derived units
   give the canonical comparison maps, compatible with restriction and with the
   transition defined by higherDirectImageOverMap. For negative q the resolutions
   have zero cohomology and every section is zero.
3. The higher-image presheaf comparison (03Q8) and sheafification of presheaf
   colimits identify the limit higher image with the sheaf colimit of the stage
   higher images. Represent a section locally by stage sections. Refine to a
   finite affine cover of V with quasi-compact pairwise fibre products. On each
   overlap, equality in the sheafification holds locally at later stages; its
   quasi-compactness reduces this to finitely many choices. Filteredness supplies
   one common stage for the local representatives and all overlap equalities.
   The stage sheaf condition glues them to a section on V (0738(4)). Its image is
   the original section because that equality holds on the cover.
4. A stage in the directed presentation is an original stage; translate the
   representative back. Naturality in steps 2 and 3 identifies its image with
   the displayed canonical transition. No diagram K or cocone B is assumed. -/
theorem exists_higher_image_affine_class_rep
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (V : S.Etale) [IsAffine V.left]
    (x : (higherDirectImage Λ (c.pt.hom ≫ k) q
      (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj.obj (op V)) :
    ∃ (i : I) (y : (higherDirectImage Λ ((D.obj i).hom ≫ k) q
      ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj.obj (op V)),
      ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op V)) y = x := by sorry

end AlgebraicGeometry.Etale
