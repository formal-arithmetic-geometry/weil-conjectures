/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
import Mathlib.CategoryTheory.Sites.Abelian
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit
import Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Local surjectivity of the higher-image colimit comparison

Source: Stacks Project, Tags 09Z1, 03Q8, 0EZM and 03FD.
(blueprint: sbc-lem-higher-image-colimit-comparison-epi).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The canonical comparison from the stage sheaf colimit is an epimorphism.
This asserts local lifting of sections; it does not assert a representative over
an entire affine object or any uniqueness of representatives.
Source: Stacks Project, Tag 09Z1, proof, using Tags 03Q8, 0EZM and 03FD.
(blueprint: sbc-lem-higher-image-colimit-comparison-epi).

Proof:
1. Choose a small directed final presentation of the filtered opposite of I.
   Its opposite is initial, so the reindexed scheme cone remains limiting.
   Base change to an affine etale object over S. The stages are qcqs, their
   transitions affine, and the limit is the corresponding pullback of c.pt.
   Inverse-image composition identifies the pulled-back coefficient diagram
   on the limit with the constant diagram on c.pt^*G. Its colimit is that sheaf
   because a nonempty filtered index is connected.
2. Compute underlying abelian cohomology with an injective module resolution.
   Its terms are acyclic for abelian sections by 03FD; no flatness of the ring
   is required. Apply complex continuity 0EZM to the degree-zero coefficient
   sheaves. A limit cohomology class over each affine basis object is the image
   of a stage class. The derived-unit construction of the cohomology maps and
   inverse-image composition identify these maps with higherDirectImageOverMap.
   In negative degrees both cohomology presheaves vanish.
3. The higher-image presheaf description 03Q8 identifies those cohomology
   presheaves, after sheafification, with the corresponding higher images.
   Consequently every section of the limit higher image lifts locally from a
   stage higher image, hence locally from the stage sheaf colimit. Local
   surjectivity is precisely epimorphy of the comparison in module sheaves.
   The equations hK and hB ensure that the map is colimit.desc K B, transported
   through eK and eB, rather than an unspecified comparison. No finite-cover
   gluing or assertion of injectivity is needed for this conclusion. -/
theorem epi_higher_image_colimit_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (K : Iᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (eK : ∀ i : I, K.obj (op i) ≅
      higherDirectImage Λ ((D.obj i).hom ≫ k) q
        ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))
    (hK : ∀ {i j : I} (f : j ⟶ i), K.map f.op =
      (eK i).hom ≫ higherDirectImageOverMap Λ k G q (D.map f) ≫ (eK j).inv)
    (B : Cocone K)
    (eB : B.pt ≅ higherDirectImage Λ (c.pt.hom ≫ k) q
      (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G))
    (hB : ∀ i : I, B.ι.app (op i) = (eK i).hom ≫
      higherDirectImageOverMap Λ k G q (c.π.app i) ≫ eB.inv)
 :
    Epi (colimit.desc K B) := by sorry

end AlgebraicGeometry.Etale
