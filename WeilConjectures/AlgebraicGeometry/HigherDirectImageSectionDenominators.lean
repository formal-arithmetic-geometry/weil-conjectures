/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.SectionCohomologyPrincipalLocalization
import WeilConjectures.AlgebraicGeometry.AffineLocalizationSheafification
import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf

/-! # Denominator bounds for higher direct image sections

## References

* Stacks Project, Tags 01XJ, 09MR and 01E4
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}} (f : X ⟶ T) (ℱ : X.Modules)
variable [QuasiCompact f] [QuasiSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- A section of a higher direct image on a principal open has a denominator bound.
(Stacks, Tags 01XJ, 09MR and 01E4) -/
theorem higherDirectImage_section_clearDenominators (q : ℕ) (W : T.Opens)
    (hW : IsAffineOpen W) (a : Γ(T, W))
    (s : Γ((higherDirectImage f q).obj ℱ, T.basicOpen a)) :
    ∃ (n : ℕ) (t : Γ((higherDirectImage f q).obj ℱ, W)),
      ((higherDirectImage f q).obj ℱ).presheaf.map
          (homOfLE (T.basicOpen_le a)).op t =
        T.presheaf.map (homOfLE (T.basicOpen_le a)).op a ^ n • s := by
  let I := injectiveResolution ℱ
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionCohomologyPresheaf K q
  let M := (higherDirectImage f q).obj ℱ
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 T.ringCatSheaf.obj)
  let c : (PresheafOfModules.sheafification (𝟙 T.ringCatSheaf.obj)).obj P ⟶ M :=
    sectionCohomologyComparison K q ≫
    (I.isoRightDerivedObj (pushforward f) q).inv
  have hc : IsIso c := (higherDirectImagePresheaf f ℱ I q).1
  let θ := A.homEquiv P M c
  have hlocal : ∀ (U : T.Opens), IsAffineOpen U → ∀ b : Γ(T, U),
      let : Module Γ(T, U) (P.obj (Opposite.op (T.basicOpen b))) :=
        Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le b)).op).hom
      IsLocalizedModule.Away b (P.map (homOfLE (T.basicOpen_le b)).op).hom := by
    intro U hU b
    exact sectionCohomologyPresheaf_isLocalized_away f ℱ I q U hU b
  have hθ (U : T.Opens) (hU : IsAffineOpen U) : IsIso (θ.app (Opposite.op U)) := by
    have hu : IsIso ((A.unit.app P).app (Opposite.op U)) :=
      affineLocalization_sheafification_unit_isIso T P hlocal U hU
    have hcU : IsIso (((SheafOfModules.forget T.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 T.ringCatSheaf.obj)).map c).app (Opposite.op U)) :=
      by
        exact (PresheafOfModules.evaluation T.ringCatSheaf.obj (Opposite.op U)).map_isIso
          ((SheafOfModules.forget T.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars (𝟙 T.ringCatSheaf.obj)).map c)
    dsimp [θ]
    erw [Adjunction.homEquiv_unit]
    change IsIso ((A.unit.app P).app (Opposite.op U) ≫ ((SheafOfModules.forget T.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 T.ringCatSheaf.obj)).map c).app (Opposite.op U))
    infer_instance
  have hθa := hθ (T.basicOpen a) (hW.basicOpen a)
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (θ.app (Opposite.op (T.basicOpen a)))).2 s
  let : Module Γ(T, W) (P.obj (Opposite.op (T.basicOpen a))) :=
    Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
  have hl := hlocal W hW a
  obtain ⟨n, y, hy⟩ := IsLocalizedModule.Away.surj
    (P.map (homOfLE (T.basicOpen_le a)).op).hom a x
  refine ⟨n, θ.app (Opposite.op W) y, ?_⟩
  change M.presheaf.map (homOfLE (T.basicOpen_le a)).op (θ.app (Opposite.op W) y) = _
  erw [← PresheafOfModules.naturality_apply θ]
  erw [← hy]
  change θ.app (Opposite.op (T.basicOpen a))
    (T.presheaf.map (homOfLE (T.basicOpen_le a)).op (a ^ n) • x) = _
  change (θ.app (Opposite.op (T.basicOpen a))).hom
      (T.presheaf.map (homOfLE (T.basicOpen_le a)).op (a ^ n) • x) = _
  erw [(θ.app (Opposite.op (T.basicOpen a))).hom.map_smul, hx]
  simp only [map_pow]

end AlgebraicGeometry.Scheme.Modules
