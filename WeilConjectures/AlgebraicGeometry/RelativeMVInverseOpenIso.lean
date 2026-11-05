/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

/-! # Explicit inverse-image open comparison

Source: Stacks Project, Cohomology, Tags 08HZ and 08HY, and Schemes, Tag 01JR.
(blueprint: lem-pc-relative-mv-inverse-open-iso).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace AlgebraicGeometry

variable [d : ∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Transport the open localization object along a specified isomorphism over X.
The unit of pullback along the isomorphism is invertible. The last comparison is
right-adjoint uniqueness for the composite adjunction, using the specified equality
of scheme morphisms. Source: Stacks, Tags 01JR, 079W and 08HZ.
(blueprint: lem-pc-relative-mv-inverse-open-iso). -/
@[irreducible] def relativeMVIsoOpenTransport {A B X : Scheme.{u}} (s : B ≅ A)
    (j : A ⟶ X) (p : B ⟶ X) (h : s.hom ≫ j = p)
    (K : schemeDerivedCategory X) :
    (schemeDerivedDirectImage j).obj ((derivedPullback j).obj K) ≅
      (schemeDerivedDirectImage p).obj ((derivedPullback p).obj K) := by
  let c := relativeMVComp s.hom j ≪≫
    eqToIso (congrArg (fun t : B ⟶ X ↦ derivedPullback t) h)
  have : IsIso (relativeMVAdj s.hom).unit := relativeMVIsoPullbackUnit_isIso s
  exact (schemeDerivedDirectImage j).mapIso
      (asIso ((relativeMVAdj s.hom).unit.app ((derivedPullback j).obj K))) ≪≫
    (schemeDerivedDirectImage s.hom ⋙ schemeDerivedDirectImage j).mapIso (c.app K) ≪≫
    ((((relativeMVAdj j).comp (relativeMVAdj s.hom)).ofNatIsoLeft c).rightAdjointUniq
      (relativeMVAdj p)).app ((derivedPullback p).obj K)

/-- The localization comparison on X', before applying any further direct image.
Source: Stacks, Tags 01JR, 079W and 08HZ.
(blueprint: lem-pc-relative-mv-inverse-open-iso). -/
@[irreducible] def relativeMVInverseOpenLocalizationIso {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (W : X.Opens) (K' : schemeDerivedCategory X') :
    (schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).obj
        ((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.obj K') ≅
      (schemeDerivedDirectImage (pullback.fst g' W.ι)).obj
        ((derivedPullback (pullback.fst g' W.ι)).obj K') :=
  (schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).mapIso
    (((mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ W)).leftAdjointUniq
      (relativeMVAdj (g' ⁻¹ᵁ W).ι)).app K') ≪≫
  relativeMVIsoOpenTransport (pullbackRestrictIsoRestrict g' W) (g' ⁻¹ᵁ W).ι
    (pullback.fst g' W.ι) (pullbackRestrictIsoRestrict_hom_ι g' W) K'

/-- The inverse-image open comparison is constructed, independent of f, K and the
object map in a base-change square. Source: Stacks, Tags 01JR, 08HZ and 08HY.
(blueprint: lem-pc-relative-mv-inverse-open-iso). -/
@[irreducible] def relativeMVInverseOpenIso {X X' S' : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (W : X.Opens) (K' : schemeDerivedCategory X') :
    (schemeDerivedDirectImage f').obj
        ((schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).obj
          ((schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.obj K')) ≅
      (schemeDerivedDirectImage (pullback.fst g' W.ι ≫ f')).obj
        ((derivedPullback (pullback.fst g' W.ι)).obj K') :=
  (schemeDerivedDirectImage f').mapIso (relativeMVInverseOpenLocalizationIso g' W K') ≪≫
  (relativeMVImageComp (pullback.fst g' W.ι) f').app
    ((derivedPullback (pullback.fst g' W.ι)).obj K')

end AlgebraicGeometry
