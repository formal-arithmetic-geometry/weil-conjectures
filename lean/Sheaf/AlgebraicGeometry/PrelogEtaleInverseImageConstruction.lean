/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PrelogLogificationData
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.MonCat.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits

/-!
# Construction of the normalized inverse image of a prelog sheaf

Source: ILO VIII, opening of §3 and §3.3.2, pp.97, 106.
(blueprint: lem-trf-prelog-etale-inverse-image-construction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable instance monoidFilteredColimits {I : Type u} [SmallCategory I]
    [IsFiltered I] : HasColimitsOfShape I CommMonCat.{u} where
  has_colimit F := HasColimit.mk
    ⟨CommMonCat.FilteredColimits.colimitCocone F,
      CommMonCat.FilteredColimits.colimitCoconeIsColimit F⟩

private theorem imageFunctions_naturality {X : Scheme.{u}} {V W : X.Etale}
    (f : V ⟶ W) :
    prelogImageFunctions W ≫ f.left.appTop =
      X.presheaf.map ((prelogEtaleImage X).map f).op ≫ prelogImageFunctions V := by
  dsimp [prelogImageFunctions]
  rw [Scheme.Hom.map_appLE]
  have hf : f.left.appTop = f.left.appLE ⊤ ⊤ (by simp) := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [hf, Scheme.Hom.appLE_comp_appLE]
  simp only [MorphismProperty.Over.w f]

/-- Sheafify the actual raw inverse-image diagram and extend its map of functions.
Source: ILO VIII, opening of §3 and §3.3.2, pp.97, 106.
(blueprint: lem-trf-prelog-etale-inverse-image-construction).

Proof: pullback of functions on the open images is natural by composition of
scheme pullbacks. Compose this with the given prelog map. The étale structure
presheaf is a sheaf, so this map extends over monoid sheafification. The
sheafification unit and its Hom equivalence give the two required normalized
properties. No witness is chosen from an unproved existence assertion. -/
theorem prelog_etale_inverse_image_construction (X : Scheme.{u})
    (P : ZariskiPrelogStructure X) : Nonempty (PrelogEtaleInverseImage P) := by
  let Q := (prelogEtaleImage X).op ⋙ P.monoidSheaf.obj
  let b : Q ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat :=
    { app := fun W ↦ P.alpha.app (op ((prelogEtaleImage X).obj W.unop)) ≫
        CommMonCat.ofHom (prelogImageFunctions W.unop).hom.toMonoidHom
      naturality := by
        intro V W f
        ext p
        have hn := ConcreteCategory.congr_hom
          (P.alpha.naturality ((prelogEtaleImage X).map f.unop).op) p
        change prelogImageFunctions W.unop
            (P.alpha.app _ (P.monoidSheaf.obj.map _ p)) =
          f.unop.left.appTop (prelogImageFunctions V.unop (P.alpha.app _ p))
        change P.alpha.app _ (P.monoidSheaf.obj.map _ p) =
          X.presheaf.map _ (P.alpha.app _ p) at hn
        exact (congrArg (prelogImageFunctions W.unop) hn).trans
          (ConcreteCategory.congr_hom (imageFunctions_naturality f.unop)
            (P.alpha.app _ p)).symm }
  have hR : Presheaf.IsSheaf X.smallEtaleTopology
      (X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.isSheaf_etaleStructurePresheaf
  have : HasSheafify (Scheme.AffineEtale.topology X) CommMonCat.{u} :=
    hasSheafifyEssentiallySmallSite (Scheme.AffineEtale.topology X) CommMonCat.{u}
  have : ((Scheme.AffineEtale.Spec X).sheafPushforwardContinuous CommMonCat.{u}
      (Scheme.AffineEtale.topology X) X.smallEtaleTopology).IsEquivalence :=
    Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _
  have : HasSheafify X.smallEtaleTopology CommMonCat.{u} :=
    Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
      (Scheme.AffineEtale.topology X) X.smallEtaleTopology (Scheme.AffineEtale.Spec X)
      (A := CommMonCat.{u})
  let α := sheafifyLift X.smallEtaleTopology b hR
  refine ⟨{
    prelog := { monoidSheaf := (presheafToSheaf X.smallEtaleTopology CommMonCat.{u}).obj Q
                alpha := α }
    unit := toSheafify X.smallEtaleTopology Q
    structural := ?_
    universal := ?_ }⟩
  · intro W p
    exact ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.app (op W)) (toSheafify_sheafifyLift _ b hR)) p
  · intro H
    exact ((sheafificationAdjunction X.smallEtaleTopology CommMonCat.{u}).homEquiv Q H).bijective

end AlgebraicGeometry
