/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundlePullbackSectionNormalization
import all WeilConjectures.AlgebraicGeometry.ProjectiveBundleRealizationPullbackTargetFrame
import all WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientPulledChartNormalization

/-! # Concrete quotient generators for realization base change
Source: Stacks Project, Tags 01NQ, 01NR and 01OB.
(blueprint: lem-pur-projective-bundle-realization-pullback-atlas-frames).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundlePullbackAdjunction projectiveBundlePullbackComp projectiveBundlePullbackCongr
  Scheme.GradedAlgebraData.relProjHom
  Scheme.GradedAlgebraData.PullbackData.relProjComparison
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
open Scheme.Modules

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
private theorem realization_chart_cover {B : Scheme.{u}} {F : B.Modules}
    (D : ProjectiveBundleRealization B F) (U : B.affineOpens) :
    (⨆ x : Γ(F, U.1), Proj.basicOpen (D.A.data.grading U)
      (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x))) = ⊤ := by
  let A := D.A.data
  let : GradedAlgebra (A.grading U) := A.gradedAlgebra U
  let a (x : Γ(F, U.1)) := D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)
  apply Proj.iSup_basicOpen_eq_top' (A.grading U) a
    (fun x ↦ ⟨1, realization_generator_mem D U x⟩)
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨y, rfl⟩ := (D.A.sectionEquiv U).surjective x
  induction y using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [(D.A.sectionEquiv U).commutes]
    exact (Algebra.adjoin (A.grading U 0) (Set.range a)).algebraMap_mem
      (algebraMap Γ(B, U.1) (A.grading U 0) r)
  | ι m => exact Algebra.subset_adjoin ⟨m, rfl⟩
  | mul a b ha hb => simpa only [map_mul] using mul_mem ha hb
  | add a b ha hb => simpa only [map_add] using add_mem ha hb

set_option maxHeartbeats 800000 in
-- Pullback comparison types retain several nested functor applications.
private theorem pulled_realization_section_free {B T : Scheme.{u}} {F : B.Modules}
    (D : ProjectiveBundleRealization B F) (r : T ⟶ D.A.data.relProj)
    (W : B.affineOpens) (x : Γ(F, W.1))
    (O : D.A.data.relProj.Opens) (hO : O ≤ D.A.data.relProjHom ⁻¹ᵁ W.1)
    (hB : D.A.data.relProjι W ⁻¹ᵁ O ≤ Proj.basicOpen (D.A.data.grading W)
      (D.A.sectionEquiv W (SymmetricAlgebra.ι _ _ x)))
    (V : T.Opens) (hV : V ≤ r ⁻¹ᵁ O)
    (hVW : V ≤ r ⁻¹ᵁ (D.A.data.relProjHom ⁻¹ᵁ W.1)) :
    IsFreeGenerator (((tensorPullback r).map D.quotient).app V
      (((tensorPullback r).obj ((tensorPullback D.A.data.relProjHom).obj F)).presheaf.map
        (homOfLE hVW).op (projectiveBundlePullbackSection r
          (projectiveBundlePullbackSection D.A.data.relProjHom x)))) := by
  have H := ProjectiveBundleQuotientGeometry.tensor_section_free r D.L O _
    (realization_chart_section_free D W x O hO hB)
  have H' := H.map hV
  rw [ProjectiveBundleQuotientGeometry.tensor_section_res, presheaf_map_map_apply] at H'
  rw [Hom.app_presheaf_map, projectiveBundlePullbackSection_eq_tensorPullbackSection,
    ProjectiveBundleQuotientGeometry.tensor_section_map]
  exact H'

set_option maxHeartbeats 2000000 in
-- Pullback comparison types retain several nested functor applications.
/-- Concrete common quotient generators for a realization pullback.

Source: Stacks Project, Tags 01NQ, 01NR and 01OB.
(blueprint: lem-pur-projective-bundle-realization-pullback-atlas-frames).

Proof: refine the affine base cover by the degree-one standard opens D_+(x). Pull each base
section x twice, first to the source relative Proj and then along b.relProjComparison, and
restrict it to the chosen open U. Define both frame sections as its quotient images. The
normalizations D.quotient_generator and D'.quotient_generator and the generator equation hb
identify these images with the twist generators x/1 and b(x)/1. Localization on D_+(x) makes
the first a free generator; the same calculation on D_+(b(x)) makes the second one free.
These opens cover: pull the source degree-one standard-open cover back by each affine Proj
map, then use the affine-pair cover of the target base. This statement asserts only a cover
and freeness for these specified sections, and no coefficient compatibility between the two
quotient maps. -/
theorem exists_projectiveBundleRealizationPullbackAtlas_frames
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data)
    (hb : ∀ (U : B.affineOpens) (U' : B'.affineOpens) (h : U'.1 ≤ g ⁻¹ᵁ U.1)
      (x : F.val.obj (op U.1)),
      b.map h (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
        D'.A.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
          (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
            (projectiveBundlePullbackSection g x))))) :
    let M := (Scheme.Modules.tensorPullback b.relProjComparison).obj
      ((Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F)
    let q := (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient
    let q' :=
      ((projectiveBundlePullbackComp b.relProjComparison D.A.data.relProjHom).app F).hom ≫
        (projectiveBundlePullbackCongr b.isPullback.w).hom.app F ≫
        ((projectiveBundlePullbackComp D'.A.data.relProjHom g).app F).inv ≫
        (Scheme.Modules.tensorPullback D'.A.data.relProjHom).map e.inv ≫ D'.quotient
    let I := Σ a : Scheme.GradedAlgebraData.PullbackData.Pairs g, Γ(F, a.1.2.1)
    let U : I → D'.A.data.relProj.Opens := fun i ↦
      D'.A.data.relProjι i.1.1.1 ''ᵁ Proj.basicOpen (D'.A.data.grading i.1.1.1)
        (b.map i.1.2 (D.A.sectionEquiv i.1.1.2 (SymmetricAlgebra.ι _ _ i.2)))
    ∃ hU : ∀ i : I,
      U i ≤ b.relProjComparison ⁻¹ᵁ (D.A.data.relProjHom ⁻¹ᵁ i.1.1.2.1),
      let m : ∀ i, Γ(M, U i) := fun i ↦ M.presheaf.map (homOfLE (hU i)).op
        (projectiveBundlePullbackSection b.relProjComparison
          (projectiveBundlePullbackSection D.A.data.relProjHom i.2))
      (⨆ i, U i) = ⊤ ∧
      (∀ i, Scheme.Modules.IsFreeGenerator (q.app (U i) (m i))) ∧
      (∀ i, Scheme.Modules.IsFreeGenerator (q'.app (U i) (m i))) := by
  classical
  intro M q q' I U
  have himage (i : I) : U i ≤ b.relProjComparison ⁻¹ᵁ
      (D.A.data.relProjι i.1.1.2 ''ᵁ Proj.basicOpen (D.A.data.grading i.1.1.2)
        (D.A.sectionEquiv i.1.1.2 (SymmetricAlgebra.ι _ _ i.2))) := by
    rintro z ⟨y, hy, rfl⟩
    have he := congrArg (fun f : Proj (D'.A.data.grading i.1.1.1) ⟶ D.A.data.relProj ↦ f y)
      (b.relProjι_relProjComparison i.1.2)
    change b.relProjComparison (D'.A.data.relProjι i.1.1.1 y) =
      D.A.data.relProjι i.1.1.2 (Proj.map (b.map i.1.2) (b.irrelevant_le_map i.1.2) y) at he
    change b.relProjComparison (D'.A.data.relProjι i.1.1.1 y) ∈
      D.A.data.relProjι i.1.1.2 ''ᵁ Proj.basicOpen (D.A.data.grading i.1.1.2)
        (D.A.sectionEquiv i.1.1.2 (SymmetricAlgebra.ι _ _ i.2))
    rw [he]
    exact ⟨_, hy, rfl⟩
  have hbase (i : I) :
      D.A.data.relProjι i.1.1.2 ''ᵁ Proj.basicOpen (D.A.data.grading i.1.1.2)
        (D.A.sectionEquiv i.1.1.2 (SymmetricAlgebra.ι _ _ i.2)) ≤
      D.A.data.relProjHom ⁻¹ᵁ i.1.1.2.1 := by
    rw [D.A.data.relProjHom_preimage]
    exact (D.A.data.relProjι i.1.1.2).image_le_opensRange _
  let hU (i : I) : U i ≤ b.relProjComparison ⁻¹ᵁ
      (D.A.data.relProjHom ⁻¹ᵁ i.1.1.2.1) :=
    (himage i).trans (b.relProjComparison.preimage_mono (hbase i))
  refine ⟨hU, ?_, ?_, ?_⟩
  · apply eq_top_iff.mpr
    intro z hz
    obtain ⟨a, ha⟩ := Scheme.GradedAlgebraData.PullbackData.Pairs.exists_mem
      (g := g) (D'.A.data.relProjHom z)
    have hza : z ∈ (D'.A.data.relProjι a.1.1).opensRange := by
      rw [← D'.A.data.relProjHom_preimage]
      exact ha
    obtain ⟨y, rfl⟩ := hza
    have hlocal : (⨆ x : Γ(F, a.1.2.1),
        Proj.basicOpen (D'.A.data.grading a.1.1)
          (b.map a.2 (D.A.sectionEquiv a.1.2 (SymmetricAlgebra.ι _ _ x)))) = ⊤ := by
      simp_rw [← Proj.map_preimage_basicOpen (b.map a.2) (b.irrelevant_le_map a.2)]
      exact (Proj.map (b.map a.2) (b.irrelevant_le_map a.2)).iSup_preimage_eq_top
        (realization_chart_cover D a.1.2)
    obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hlocal.ge (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, x⟩, y, hx, rfl⟩
  · intro i
    exact pulled_realization_section_free D b.relProjComparison i.1.1.2 i.2 _ (hbase i)
      (le_of_eq ((D.A.data.relProjι i.1.1.2).preimage_image_eq _)) (U i) (himage i) (hU i)
  · intro i
    exact projectiveBundleRealizationPullback_target_frame D D' g e b hb
      i.1.1.2 i.1.1.1 i.1.2 i.2 (hU i)

end AlgebraicGeometry
