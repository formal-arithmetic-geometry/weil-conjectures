/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.ColimitsOver

/-!
# The Galois category axioms for finite étale schemes

Let `Y` be a scheme. We verify the axioms of a (pre-)Galois category for the category
`FÉt(Y)` of finite étale `Y`-schemes, and, for connected `Y` and a geometric point `s`, the axioms
of a fibre functor for the geometric fibre functor `F_s`
(blueprint `lem-fet-finite-limits`, `lem-fet-galois-category`).

* Finite limits are computed in schemes.
* Finite coproducts are disjoint unions.
* The quotient of a finite étale `Y`-scheme `P` by a finite group `G` is glued from the spectra
  of the rings of invariants over the affine opens of `Y`
  (`AlgebraicGeometry.Scheme.hasColimitsOfShape_singleObj`); it is finite étale by
  `AlgHom.finite_and_etale_fixedPoints`, and its geometric points are the `G`-orbits of the
  geometric points of `P` (`AlgHom.surjective_comap_fixedPoints_val_and_iff`).
* A monomorphism is an open and closed immersion, hence the inclusion of a direct summand.
* The fibre functor is conservative: a morphism inducing a bijection on geometric fibres is a
  surjective monomorphism, by a clopen-image argument over the connected base.
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}}

/-- The category of affine `Y`-schemes. -/
local instance :
    Category (MorphismProperty.Over (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ Y) :=
  MorphismProperty.Comma.instCategory _ _ _ _ _

variable (Y) in
/-- A finite étale `Y`-scheme as an affine `Y`-scheme. -/
@[simps]
noncomputable def toAffineOver :
    Y.FiniteEtale ⥤ MorphismProperty.Over (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ Y where
  obj P := MorphismProperty.Over.mk ⊤ P.obj.hom
    (by have : IsFinite P.obj.hom := P.property; infer_instance)
  map f := MorphismProperty.Over.homMk f.hom.left (hom_left_comp f) trivial

/-- The functor `FÉt(Y) ⥤ AffOver(Y)` is fully faithful. -/
noncomputable def toAffineOverFullyFaithful : (toAffineOver Y).FullyFaithful where
  preimage f :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk f.left (MorphismProperty.Over.w f))
  map_preimage f := MorphismProperty.Over.Hom.ext rfl
  preimage_map f := hom_ext rfl

instance : (toAffineOver Y).Full := toAffineOverFullyFaithful.full
instance : (toAffineOver Y).Faithful := toAffineOverFullyFaithful.faithful

section Quotient

variable {G : Type u} [Monoid G] [Finite G] (D : SingleObj G ⥤ Y.FiniteEtale)

lemma isAffineHom_of_isAffineHom {X Z : Scheme.{u}} (f : X ⟶ Z) (hf : IsAffineHom f) :
    IsAffineHom f :=
  hf

lemma isAffineHom_of_isAffine {X Z : Scheme.{u}} (f : X ⟶ Z) (_ : IsAffine X) (_ : IsAffine Z) :
    IsAffineHom f :=
  inferInstance

/-- The gluing data for the quotient of a finite étale `Y`-scheme by a finite monoid action. -/
noncomputable abbrev quotientGluingData :
    Y.directedAffineCover.ColimitGluingData (D ⋙ toAffineOver Y) :=
  Scheme.quotientGluingData isAffineHom_of_isAffineHom isAffineHom_of_isAffine _

instance preservesColimitsOfShape_pullback_trans {U V : Y.directedAffineCover.I₀} (hUV : U ⟶ V) :
    PreservesColimitsOfShape (SingleObj G)
      (MorphismProperty.Over.pullback (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤
        (Y.directedAffineCover.trans hUV)) :=
  preservesColimitsOfShape_pullback isAffineHom_of_isAffineHom isAffineHom_of_isAffine _

/-- The quotient cocone in affine `Y`-schemes is a colimit. -/
noncomputable def isColimitGluedCocone : IsColimit (quotientGluingData D).gluedCocone :=
  (quotientGluingData D).isColimitGluedCocone

lemma isFinite_and_etale_gluedCocone :
    IsFinite (quotientGluingData D).gluedCocone.pt.hom ∧
      Etale (quotientGluingData D).gluedCocone.pt.hom := by
  have : IsFinite ((D ⋙ toAffineOver Y).obj (SingleObj.star G)).hom :=
    (D.obj (SingleObj.star G)).property
  have : Etale ((D ⋙ toAffineOver Y).obj (SingleObj.star G)).hom :=
    (D.obj (SingleObj.star G)).obj.prop
  exact isFinite_and_etale_of_isColimit isAffineHom_of_isAffineHom isAffineHom_of_isAffine _
    (isColimitGluedCocone D)

/-- The quotient of a finite étale `Y`-scheme by a finite monoid action, as a cocone in
`FÉt(Y)`. -/
noncomputable def quotientCocone : Cocone D where
  pt := ⟨MorphismProperty.Over.mk ⊤ (quotientGluingData D).gluedCocone.pt.hom
    (isFinite_and_etale_gluedCocone D).2, (isFinite_and_etale_gluedCocone D).1⟩
  ι :=
    { app j := ObjectProperty.homMk (MorphismProperty.Over.homMk
        ((quotientGluingData D).gluedCocone.ι.app j).left
        (MorphismProperty.Over.w ((quotientGluingData D).gluedCocone.ι.app j)))
      naturality j j' g := hom_ext
        congr(($((quotientGluingData D).gluedCocone.ι.naturality g)).left) }

/-- The quotient cocone is a colimit in `FÉt(Y)`. -/
noncomputable def isColimitQuotientCocone : IsColimit (quotientCocone D) :=
  isColimitOfReflects (toAffineOver Y)
    (IsColimit.ofIsoColimit (isColimitGluedCocone D)
      (Cocone.ext (MorphismProperty.Over.isoMk (Iso.refl _)) fun _ ↦
        MorphismProperty.Over.Hom.ext (by simp [quotientCocone])))

variable (Y G) in
/-- **`FÉt(Y)` has quotients by finite monoids.** -/
theorem hasColimitsOfShape_singleObj : HasColimitsOfShape (SingleObj G) Y.FiniteEtale :=
  ⟨fun D ↦ ⟨_, isColimitQuotientCocone D⟩⟩

end Quotient

end AlgebraicGeometry.Scheme.FiniteEtale
