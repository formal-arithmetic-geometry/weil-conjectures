/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.HigherImageCohomologyPresheafLocalization
import WeilConjectures.AlgebraicGeometry.AffineLocalizingPresheafSheafification
import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf

/-! # Power torsion for higher direct image sections

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A higher direct image section vanishing on a principal open is power torsion.
(Stacks, Tags 01XJ, 09MR and 01E4) -/
theorem higherDirectImage_section_pow_annihilates (q : ℕ) (W : T.Opens)
    (hW : IsAffineOpen W) (a : Γ(T, W))
    (t : Γ((higherDirectImage f q).obj ℱ, W))
    (ht : ((higherDirectImage f q).obj ℱ).presheaf.map
      (homOfLE (T.basicOpen_le a)).op t = 0) :
    ∃ n : ℕ, a ^ n • t = 0 := by
  let I := injectiveResolution ℱ
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionCohomologyPresheaf K q
  let M := (higherDirectImage f q).obj ℱ
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 T.ringCatSheaf.obj)
  let c := sectionCohomologyComparison K q ≫ (I.isoRightDerivedObj (pushforward f) q).inv
  let hc : IsIso c := (higherDirectImagePresheaf f ℱ I q).1
  let θ : P ⟶ (SheafOfModules.forget T.ringCatSheaf).obj M := A.homEquiv P M c
  have hP (V : T.Opens) (hV : IsAffineOpen V) (b : Γ(T, V)) :
      IsLocalizedModule.Away b (P.map (homOfLE (T.basicOpen_le b)).op).hom :=
    higherImageCohomologyPresheaf_isLocalized f ℱ I q V hV b
  have hθ (V : T.Opens) (hV : IsAffineOpen V) : IsIso (θ.app (Opposite.op V)) := by
    let hu := isIso_sheafificationUnit_app_of_affine_localizing T P hP V hV
    change IsIso (((A.unit.app P).app (Opposite.op V)) ≫
      ((SheafOfModules.forget T.ringCatSheaf).map c).app (Opposite.op V))
    have hv : IsIso (((SheafOfModules.forget T.ringCatSheaf).map c).app
        (Opposite.op V)) :=
      (PresheafOfModules.evaluation T.ringCatSheaf.obj (Opposite.op V)).map_isIso
        ((SheafOfModules.forget T.ringCatSheaf).map c)
    let : IsIso ((A.unit.app P).app (Opposite.op V)) := hu
    let : IsIso (((SheafOfModules.forget T.ringCatSheaf).map c).app
        (Opposite.op V)) := hv
    infer_instance
  have hθW := hθ W hW
  have hθD := hθ (T.basicOpen a) (hW.basicOpen a)
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (θ.app (Opposite.op W))).2 t
  have hx0 : P.map (homOfLE (T.basicOpen_le a)).op x = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (θ.app (Opposite.op (T.basicOpen a)))).1
    have hn := ConcreteCategory.congr_hom
      (θ.naturality (homOfLE (T.basicOpen_le a)).op) x
    change θ.app (Opposite.op (T.basicOpen a))
        (P.map (homOfLE (T.basicOpen_le a)).op x) =
      M.presheaf.map (homOfLE (T.basicOpen_le a)).op
        (θ.app (Opposite.op W) x) at hn
    rw [hx, ht] at hn
    simpa only [map_zero] using hn
  have := hP W hW a
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers a)
      (P.map (homOfLE (T.basicOpen_le a)).op).hom).mp hx0
  refine ⟨n, ?_⟩
  have he := congrArg (θ.app (Opposite.op W)) hn
  change (θ.app (Opposite.op W)).hom (a ^ n • x) =
    (θ.app (Opposite.op W)).hom 0 at he
  rw [_root_.map_smul, map_zero] at he
  exact hx ▸ he

end AlgebraicGeometry.Scheme.Modules
