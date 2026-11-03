/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Identity normalization of the relative product compositor

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, clause (iv).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem relative_comp_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h] [QuasiCompact f] [QuasiCompact h] :
    letI : HasCompactification (f ≫ g) := .of_eq w.symm
    letI : QuasiCompact (f ≫ g) := by rw [w]; infer_instance
    rightDerivedLowerShriekCompIsoOfEq Λ f g h w =
      (unboundedEtaleLowerShriekCongr Λ w).symm ≪≫
        (unboundedEtaleLowerShriekCompIso Λ f g).symm := by
  subst h
  apply Iso.ext
  simp only [rightDerivedLowerShriekCompIsoOfEq, unboundedEtaleLowerShriekCongr,
    eqToIso_refl, Iso.refl_trans, Iso.refl_symm, rightDerivedLowerShriekCompIso,
    unboundedEtaleLowerShriekCompIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, Category.assoc]
  rfl

private theorem compactSupportCongr_symm
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    unboundedEtaleLowerShriekCongr Λ w.symm =
      (unboundedEtaleLowerShriekCongr Λ w).symm := by
  subst w
  simp only [unboundedEtaleLowerShriekCongr, Iso.refl_symm]

/-- The inverse right-unit compositor is the canonical compact-support identity comparison.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, identity-composition clause
(blueprint: lem-sf-relative-kunneth-identity-comparisons).

Proof: identify the raw relative-product compositor with the inverse of the canonical
unbounded compact-support compositor. Apply its right unit law, evaluate at the input,
and cancel the congruence comparison for f followed by the identity. -/
theorem relativeKunnethCompIsoApp_id_inv
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (M : DerivedCategoryModule Λ X) :
    (rightDerivedLowerShriekCompIsoApp Λ f (𝟙 Y) f (by simp) M).inv =
      (unboundedEtaleLowerShriekId Λ Y).hom.app
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) := by
  have h := (unboundedEtaleLowerShriekCompIso_units Λ f).2
  rw [rightDerivedLowerShriekCompIsoApp, relative_comp_eq]
  simp only [Iso.app_inv, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  rw [compactSupportCongr_symm Λ (Category.comp_id f)] at h
  rw [h]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  exact Category.comp_id _

end AlgebraicGeometry.Etale
