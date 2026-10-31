/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundlePullbackSectionNormalization
import all WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientPulledChartNormalization
import all WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistExistence
import all WeilConjectures.AlgebraicGeometry.ProjectiveBundleRealizationPullbackTargetFrame
import all WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjPullbackNormalizedChartFactor

/-! # Images of generators in the normalized affine-pair twist comparison
(blueprint: lem-pur-projective-bundle-realization-pullback-chart-images). -/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2048
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
open Scheme.Modules
open SymmetricProjTautologicalCharts
attribute [local irreducible] tensorPullback projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction
  Scheme.GradedAlgebraData.relProjHom Scheme.GradedAlgebraData.relProjι
  Scheme.GradedAlgebraData.relProj
  Scheme.GradedAlgebraData.PullbackData.relProjComparison
  Proj Proj.map Proj.twist Proj.unitToTwist Proj.twistPullbackMap

set_option maxHeartbeats 2000000 in
-- The calculation retains the normalized pullback comparison types.
/-- The concrete homogeneous-fraction map intertwines the quotient images of each
specified base section on an affine-pair chart.

Source: Stacks Project, Tags 01MY, 01NQ, 01NR and 01OB.
(blueprint: lem-pur-projective-bundle-realization-pullback-chart-images).

Proof: conjugate the pointwise homogeneous-localization map on degree-one twists by the
two realization charts and the normalized tensor pullback comparisons. On a pulled base
section, the source chart gives x/1. The fraction map sends it to b(x)/1; hb identifies this
with the degree-one generator in the target chart. Naturality and the adjunction unit
normalization identify the remaining composition maps with the specified quotient maps.
Only these specified sections are compared; no generation by affine global sections is used. -/
theorem projectiveBundleRealizationPullback_chart_images
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data)
    (hb : ∀ (U : B.affineOpens) (U' : B'.affineOpens) (h : U'.1 ≤ g ⁻¹ᵁ U.1)
      (x : F.val.obj (op U.1)),
      b.map h (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
        D'.A.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
          (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
            (projectiveBundlePullbackSection g x)))))
    (W : B.affineOpens) (W' : B'.affineOpens) (h : W'.1 ≤ g ⁻¹ᵁ W.1) :
    let M := (tensorPullback b.relProjComparison).obj
      ((tensorPullback D.A.data.relProjHom).obj F)
    let P := (tensorPullback b.relProjComparison).obj D.L
    let q := (tensorPullback b.relProjComparison).map D.quotient
    let q' :=
      ((projectiveBundlePullbackComp b.relProjComparison D.A.data.relProjHom).app F).hom ≫
        (projectiveBundlePullbackCongr b.isPullback.w).hom.app F ≫
        ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
        (tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient
    ∃ v : (tensorPullback (D'.A.data.relProjι W')).obj P ⟶
        (tensorPullback (D'.A.data.relProjι W')).obj D'.L,
      ∀ (V : D'.A.data.relProj.Opens)
        (hS : V ≤ b.relProjComparison ⁻¹ᵁ (D.A.data.relProjHom ⁻¹ᵁ W.1))
        (_hT : V ≤ D'.A.data.relProjHom ⁻¹ᵁ W'.1) (x : Γ(F, W.1)),
        let m := M.presheaf.map (homOfLE hS).op
          (projectiveBundlePullbackSection b.relProjComparison
            (projectiveBundlePullbackSection D.A.data.relProjHom x))
        v.app (D'.A.data.relProjι W' ⁻¹ᵁ V)
          (tensorPullbackSection (D'.A.data.relProjι W') P V (q.app V m)) =
            tensorPullbackSection (D'.A.data.relProjι W') D'.L V (q'.app V m) := by
  classical
  intro M P q q'
  let j := D.A.data.relProjι W
  let j' := D'.A.data.relProjι W'
  let r := Proj.map (b.map h) (b.irrelevant_le_map h)
  have hr : j' ≫ b.relProjComparison = r ≫ j := b.relProjι_relProjComparison h
  let θ := Proj.twistPullbackMap (b.map h) (b.irrelevant_le_map h) 1
  let v : (tensorPullback j').obj P ⟶ (tensorPullback j').obj D'.L :=
    (tensor_comp_app j' b.relProjComparison D.L).inv ≫
      line_transport (j' ≫ b.relProjComparison) r j hr D.L ≫
        (tensorPullback r).map (D.twists.chart W).hom ≫ θ ≫ (D'.twists.chart W').inv
  refine ⟨v, ?_⟩
  intro V hS hT x m
  let O := j' ⁻¹ᵁ V
  have hOr : O ≤ r ⁻¹ᵁ (j ⁻¹ᵁ (D.A.data.relProjHom ⁻¹ᵁ W.1)) := by
    have he := congrArg (fun f ↦ f ⁻¹ᵁ (D.A.data.relProjHom ⁻¹ᵁ W.1)) hr
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage] at he
    exact (j'.preimage_mono hS).trans he.le
  have hs : q.app V m = P.presheaf.map (homOfLE hS).op
      (tensorPullbackSection b.relProjComparison D.L (D.A.data.relProjHom ⁻¹ᵁ W.1)
        (D.quotient.app (D.A.data.relProjHom ⁻¹ᵁ W.1)
          (projectiveBundlePullbackSection D.A.data.relProjHom x))) := by
    dsimp only [q, m]
    erw [Hom.app_presheaf_map, section_naturality]
    rw [projectiveBundlePullbackSection_eq_tensorPullbackSection]
  rw [hs, ProjectiveBundleQuotientGeometry.tensor_section_res]
  have hv := chart_transport_section b.relProjComparison j j' r hr D.L D'.L
    (D.twists.chart W) (D'.twists.chart W') θ (D.A.data.relProjHom ⁻¹ᵁ W.1)
    O (j'.preimage_mono hS) hOr
    (D.quotient.app (D.A.data.relProjHom ⁻¹ᵁ W.1)
      (projectiveBundlePullbackSection D.A.data.relProjHom x))
  change v.app O _ = _ at hv
  dsimp only [sectionOn] at hv
  rw [hv]
  apply_fun (fun s ↦ (D'.twists.chart W').hom.app O s) using
    (ConcreteCategory.bijective_of_isIso _).injective
  dsimp only
  erw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id]
  simp only [Hom.id_app, ConcreteCategory.id_apply]
  have hgen := realization_chart_section D W (D.A.data.relProjHom ⁻¹ᵁ W.1) le_rfl x
  simp only [Scheme.Modules.presheaf_map_id_apply] at hgen
  have ht := twist_map_generator_on (b.map h) (b.irrelevant_le_map h)
    (D.A.sectionEquiv W (SymmetricAlgebra.ι _ _ x)) (realization_generator_mem D W x)
    (j ⁻¹ᵁ (D.A.data.relProjHom ⁻¹ᵁ W.1)) O hOr
  have hg : (⟨b.map h (D.A.sectionEquiv W (SymmetricAlgebra.ι _ _ x)),
      (b.map h).map_mem (realization_generator_mem D W x)⟩ : D'.A.data.grading W' 1) =
      ⟨D'.A.sectionEquiv W' (SymmetricAlgebra.ι _ _
        (e.inv.app W'.1 (((tensorPullback g).obj F).presheaf.map (homOfLE h).op
          (projectiveBundlePullbackSection g x)))),
        realization_generator_mem D' W' _⟩ := by
    exact Subtype.ext (hb W W' h x)
  rw [hgen]
  refine ht.trans ?_
  rw [show (Proj.unitToTwist ((b.map h).map_mem (realization_generator_mem D W x))).app O
      (unitSectionsEquiv O 1) = _ from congrArg
        (fun a : D'.A.data.grading W' 1 ↦ (Proj.unitToTwist a.property).app O
          (unitSectionsEquiv O 1)) hg]
  have he := section_square_quotient b.relProjComparison D.A.data.relProjHom
    D'.A.data.relProjHom g b.isPullback.w e.inv D'.quotient h hT hS x
  rw [he]
  exact (realization_chart_section D' W' V hT _).symm

end AlgebraicGeometry
