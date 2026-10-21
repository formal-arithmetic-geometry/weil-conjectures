/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Derived module evaluation as abelian cohomology on the slice

Source: Stacks Project, Cohomology on Sites, Tags 03FD and 03F3(2)
(blueprint: lem-pe-ringed-site-derived-evaluation-slice).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Derived evaluation of left module sheaves is canonically the abelian cohomology
of their sectionwise restriction to the slice. The natural isomorphisms include all
module sheaves simultaneously. Their degree-zero equation identifies the two
augmentations from `M(W)`. The final equation specifies the canonical comparison
on every augmentation-compatible lift from a module resolution to an abelian
resolution on the slice; it is independent of the chosen resolutions and lift.

Source: Stacks Project, Cohomology on Sites, Tags 03FD and 03F3(2)
(blueprint: lem-pe-ringed-site-derived-evaluation-slice).

Proof:
1. Apply lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison at W.
   This gives the natural, degree-zero-normalized comparison from module derived
   evaluation to abelian derived evaluation on C. Only evaluation acyclicity of
   forgotten injective modules is needed, not their injectivity as abelian sheaves.
2. Choose an abelian injective resolution of the forgotten module. Restriction
   to C/W is exact by lem-weil-pbc-site-restriction-injectives and preserves
   abelian injectives by lem-weil-pbc-cohomology-over-object-localization.
   Consequently its restriction is an abelian injective resolution on C/W.
3. The object id_W is terminal in C/W. Evaluating the restricted resolution at
   id_W gives the identical complex of abelian groups obtained by evaluating the
   original resolution at W. Comparison lifts give identical evaluated chain
   maps, proving independence, naturality, and degree-zero identity for this
   abelian localization comparison.
4. Compose the comparison of step 1 with that of step 3. Naturality squares
   paste, and the two degree-zero identities compose to the displayed equation.
   Comparison lifts induce the specified homology map for any module resolution
   and slice abelian resolution. Neither flatness over the integer sheaf nor
   injectivity of the forgotten module is used.
-/
theorem module_derived_evaluation_slice
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u}) [EnoughInjectives (ringedSiteModules.{u} R)] (W : C) :
    ∃ e : ∀ q : ℕ,
      (SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W))).rightDerived q ≅
      (SheafOfModules.toSheaf R ⋙ J.overPullback AddCommGrpCat.{u} W) ⋙
        (sheafToPresheaf (J.over W) AddCommGrpCat.{u} ⋙
          (evaluation (Over W)ᵒᵖ AddCommGrpCat.{u}).obj
            (op (Over.mk (𝟙 W)))).rightDerived q,
      ((SheafOfModules.toSheaf R ⋙
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W))).toRightDerivedZero ≫
          (e 0).hom =
        Functor.whiskerLeft
          (SheafOfModules.toSheaf R ⋙ J.overPullback AddCommGrpCat.{u} W)
          ((sheafToPresheaf (J.over W) AddCommGrpCat.{u} ⋙
            (evaluation (Over W)ᵒᵖ AddCommGrpCat.{u}).obj
              (op (Over.mk (𝟙 W)))).toRightDerivedZero)) ∧
      ∀ (M : ringedSiteModules.{u} R) (I : InjectiveResolution M)
        (K : InjectiveResolution
          ((SheafOfModules.toSheaf R ⋙ J.overPullback AddCommGrpCat.{u} W).obj M))
        (φ : ((SheafOfModules.toSheaf R ⋙ J.overPullback AddCommGrpCat.{u} W).mapHomologicalComplex
          (.up ℕ)).obj I.cocomplex ⟶ K.cocomplex)
        (_hφ : (SheafOfModules.toSheaf R ⋙ J.overPullback AddCommGrpCat.{u} W).map
          (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0) (q : ℕ),
        (e q).hom.app M ≫
            (K.isoRightDerivedObj
              (sheafToPresheaf (J.over W) AddCommGrpCat.{u} ⋙
                (evaluation (Over W)ᵒᵖ AddCommGrpCat.{u}).obj
                  (op (Over.mk (𝟙 W)))) q).hom =
          (I.isoRightDerivedObj
            (SheafOfModules.toSheaf R ⋙
              (sheafToPresheaf J AddCommGrpCat.{u} ⋙
                (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op W))) q).hom ≫
            HomologicalComplex.homologyMap
              (((sheafToPresheaf (J.over W) AddCommGrpCat.{u} ⋙
                (evaluation (Over W)ᵒᵖ AddCommGrpCat.{u}).obj
                  (op (Over.mk (𝟙 W)))).mapHomologicalComplex (.up ℕ)).map φ) q := by
  let A := SheafOfModules.toSheaf R
  let B := J.overPullback AddCommGrpCat.{u} W
  let T := A ⋙ B
  let F := sheafToPresheaf (J.over W) AddCommGrpCat.{u} ⋙
    (evaluation (Over W)ᵒᵖ AddCommGrpCat.{u}).obj (op (Over.mk (𝟙 W)))
  let : EnoughInjectives (Sheaf J AddCommGrpCat.{u}) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} J AddCommGrpCat.{u})
  let : HasExt.{u} (Sheaf J AddCommGrpCat.{u}) := hasExt_of_enoughInjectives _
  let : EnoughInjectives (Sheaf (J.over W) AddCommGrpCat.{u}) :=
    @IsGrothendieckAbelian.enoughInjectives _ _ _
      (Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} (J.over W) AddCommGrpCat.{u})
  let : HasExt.{u} (Sheaf (J.over W) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  have : B.Additive := by
    constructor
    intro X Y f g
    ext V
    rfl
  have : B.IsLeftAdjoint :=
    ((Over.forget W).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (J.over W) J).isLeftAdjoint
  have hT (I : ringedSiteModules.{u} R) [Injective I] :
      F.rightAcyclic (T.obj I) := by
    intro n
    let : Subsingleton (Sheaf.H' (A.obj I) (n + 1) W) :=
      injective_module_abelian_acyclic W I (n + 1) (Nat.succ_pos n)
    obtain ⟨a⟩ := cohomology_over_object_localization (A.obj I) W (n + 1)
    have hz : IsZero (Sheaf.H' (B.obj (A.obj I)) (n + 1) (Over.mk (𝟙 W))) :=
      (AddCommGrpCat.isZero_of_subsingleton _).of_iso a.symm
    obtain ⟨d⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
      (J.over W) (Over.mk (𝟙 W)) (n + 1)
    exact hz.of_iso (d.app (T.obj I)).symm
  refine ⟨fun q ↦ exact_comp_comparison T F hT q,
    exact_comp_comparison_zero T F hT, ?_⟩
  intro M I K φ hφ q
  exact exact_comp_comparison_formula T F hT M I K φ hφ q

end CategoryTheory
