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

/-! # Eventual vanishing of affine higher-image sections

Source: Stacks Project, Tags 09Z1, 03Q8 and 0738.
(blueprint: sbc-lem-higher-image-affine-class-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- A stage section with zero limit image becomes zero at a later stage.
Source: Stacks Project, Tag 09Z1, proof; Tag 0738(2).
(blueprint: sbc-lem-higher-image-affine-class-vanishing).

Proof:
1. Replace the filtered opposite index by a directed final presentation, keeping
   the scheme limit by opposite initiality. After base change to an affine etale
   object, the stages are qcqs with affine transitions. The pulled-back coefficient
   diagram on the limit identifies by inverse-image composition with the constant
   diagram of the pullback of G, whose colimit is that sheaf.
2. Compute underlying abelian cohomology by an injective module resolution, using
   its abelian-section acyclicity (03FD). Complex continuity (0EZM), applied to
   degree-zero sheaves, gives continuity of the restricted cohomology presheaves
   on the affine basis. The maps come from derived units, hence commute with
   restriction and are precisely higherDirectImageOverMap after the higher-image
   presheaf identification (03Q8). Negative degrees vanish. Sheafification of
   presheaf colimits identifies the limit higher image with the stage sheaf colimit.
3. If a stage section has zero limit image, equality with zero in the associated
   sheaf is locally witnessed at later stages. Refine the witnessing cover of V
   to a finite affine cover. Move these finitely many witnesses to a common later
   stage using filteredness. At that stage the section restricts to zero on every
   cover member, so separatedness of the stage sheaf makes it zero on V (0738(2)).
4. For an original stage i, finality first gives an arrow in the filtered opposite
   category from i to a reindexed stage. Perform step 3 there and compose the two
   arrows. This is a morphism j to i in the original cofiltered category, and
   functoriality of the canonical transitions gives exactly the displayed zero. -/
theorem exists_higher_image_affine_class_eq_zero
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (V : S.Etale) [IsAffine V.left] (i : I)
    (y : (higherDirectImage Λ ((D.obj i).hom ≫ k) q
      ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj.obj (op V))
    (hy : ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op V)) y = 0) :
    ∃ (j : I) (f : j ⟶ i),
      ((higherDirectImageOverMap Λ k G q (D.map f)).hom.app (op V)) y = 0 := by sorry

end AlgebraicGeometry.Etale
