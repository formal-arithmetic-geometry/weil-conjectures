/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Open-restriction normalization for the comparison adjunction unit

Source: literature/stacks-project/sites.tex, Tag 00WX (lemma-adjoint-sheaves),
with the open restriction normalization extracted from the comparison-pullback
construction (blueprint: lem-pur-comparison-pullback-open-unit).

The comparison `gamma` is the canonical conjugate of the sectionwise identity
on direct images.  Its inverse is `a`, and `c` is the fixed restriction
identification between the two direct-image composites.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The canonical comparison `gamma` for an open immersion, obtained by the
conjugate construction from the sectionwise direct-image identity.
Source: Stacks Project, Tag 00WX; (blueprint: lem-pur-comparison-pullback-open-unit). -/
noncomputable abbrev comparisonPullbackOpenUnitGamma (A : Type (u + 1)) [CommRing A]
    [Finite A] {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] :
    Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) V ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j :=
  openComparisonRestrictionIso A j

/-- The inverse `a = gamma⁻¹` of the canonical open comparison.
Source: Stacks Project, Tag 00WX; (blueprint: lem-pur-comparison-pullback-open-unit). -/
noncomputable abbrev comparisonPullbackOpenUnitA (A : Type (u + 1)) [CommRing A]
    [Finite A] {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] :
    comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j ≅
      Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) V :=
  (comparisonPullbackOpenUnitGamma A j).symm

/-- The fixed restriction identification `c` on direct images.
Source: Stacks Project, Tag 00WX; (blueprint: lem-pur-comparison-pullback-open-unit). -/
noncomputable abbrev comparisonPullbackOpenUnitC (A : Type (u + 1)) [CommRing A]
    [Finite A] {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] :
    comparisonLowerStar (ModuleCat.{u + 1} A) T ⋙
        Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ≅
      ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonLowerStar (ModuleCat.{u + 1} A) V :=
  comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma comparisonPullbackOpenUnit_conjugate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    conjugateEquiv
      ((comparisonAdjunction (ModuleCat.{u + 1} A) X).comp
        (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j))
      ((Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (comparisonAdjunction (ModuleCat.{u + 1} A) U))
      (openComparisonRestrictionIso A j).hom =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) j).hom := by
  let B := ModuleCat.{u + 1} A
  let r₀ := Etale.upperStarLowerStarAdjunction B j
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s₀ := upperStarLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  let cU := comparisonAdjunction B U
  let cX := comparisonAdjunction B X
  change conjugateEquiv (cX.comp s) (r.comp cU)
    (Functor.whiskerRight (Etale.upperStarIsoOpenImmersionRestriction B j).inv _ ≫
      (supportSiteComparisonCoefficientPullbackIso B j).hom ≫
        Functor.whiskerLeft (comparisonUpperStar B X)
          (upperStarIsoOpenImmersionRestriction B j).hom) = _
  rw [← conjugateEquiv_comp (cX.comp s) (r₀.comp cU) (r.comp cU),
    ← conjugateEquiv_comp (cX.comp s) (cX.comp s₀) (r₀.comp cU),
    conjugateEquiv_whiskerLeft s s₀ cX
      (upperStarIsoOpenImmersionRestriction B j).hom,
    conjugateEquiv_whiskerRight r₀ r cU
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv]
  have he : conjugateEquiv r₀ r
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  have hp : conjugateEquiv s s₀
      (upperStarIsoOpenImmersionRestriction B j).hom = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  rw [he, hp]
  change (𝟙 _ ≫ (conjugateEquiv (cX.comp s₀) (r₀.comp cU))
    (supportSiteComparisonCoefficientPullbackIso B j).hom) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  exact congrArg Iso.inv
    ((conjugateIsoEquiv (r₀.comp cU) (cX.comp s₀)).apply_symm_apply
      (supportSiteComparisonCoefficientDirectImageIso B j).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma comparisonPullbackOpenUnit_directImage_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk _ _ _ _
        (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j).hom)
      ).natTrans =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) j).hom := by
  ext M : 2
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  simp only [Functor.comp_obj, mateEquiv_apply, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom]
  change M.obj.map _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ M.obj.map _)) =
    𝟙 _ ≫ M.obj.map _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply Limits.pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullback, Scheme.toProEt,
      supportSiteComparisonSiteBaseChangeIso]
  rfl

/-- For every etale module sheaf `F` on `T`, the comparison adjunction unit
is preserved by restriction to the open `V`.  The first map is the etale
restriction of `eta^T_F`; `c` is the fixed sectionwise restriction
identification; and `a = gamma⁻¹`, where `gamma` is the conjugate of the
sectionwise direct-image identity.

Source: literature/stacks-project/sites.tex, Tag 00WX (lemma-adjoint-sheaves),
and the open restriction normalization of the comparison pullback
(blueprint: lem-pur-comparison-pullback-open-unit).

Proof: identify both right adjoints on an etale object over `V` with the
sections on its fibre product with `V`, so `c` is the identity.  Expand the
units of the two composite adjunctions and apply the conjugate-isomorphism
unit equation to the canonical comparison `gamma`.  Evaluate the resulting
identity on every etale object over `V` and cancel `gamma` using `a = gamma⁻¹`.
This gives the displayed equality, and equality on all components is equality
of sheaf morphisms.
(blueprint: lem-pur-comparison-pullback-open-unit). -/
theorem comparisonPullbackOpenUnit (A : Type (u + 1)) [CommRing A]
    [Finite A] {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] :
    ∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map
          ((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F) ≫
        (comparisonPullbackOpenUnitC A j).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) V).map
          ((comparisonPullbackOpenUnitA A j).hom.app F) =
      (comparisonAdjunction (ModuleCat.{u + 1} A) V).unit.app
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F) := by
  intro F
  let B := ModuleCat.{u + 1} A
  let cV := comparisonAdjunction B V
  let cT := comparisonAdjunction B T
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  let α := TwoSquare.mk _ _ _ _ (openComparisonRestrictionIso A j).hom
  let θ := TwoSquare.mk _ _ _ _ (comparisonLowerStarOpenImmersionRestrictionIso B j).hom
  have h : mateEquiv cT cV α = θ := by
    apply (mateEquiv s r).injective
    apply (TwoSquare.equivNatTrans _ _ _ _).injective
    change (mateEquiv s r (mateEquiv cT cV α)).natTrans =
      (mateEquiv s r θ).natTrans
    rw [iterated_mateEquiv_conjugateEquiv]
    exact (comparisonPullbackOpenUnit_conjugate A j).trans
      (comparisonPullbackOpenUnit_directImage_mate A j).symm
  have hu := unit_mateEquiv cT cV α F
  rw [h] at hu
  change (Etale.openImmersionRestriction B j).map (cT.unit.app F) ≫
    (comparisonPullbackOpenUnitC A j).hom.app _ =
      cV.unit.app _ ≫ (comparisonLowerStar B V).map
        ((comparisonPullbackOpenUnitGamma A j).hom.app F) at hu
  rw [reassoc_of% hu, ← Functor.map_comp]
  simp
  rfl

end AlgebraicGeometry.ProEtale
