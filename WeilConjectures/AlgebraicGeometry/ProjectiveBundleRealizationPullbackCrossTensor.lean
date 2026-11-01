/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.TensorPullbackCrossTensorGenerators
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleRealizationPullbackChartImages
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleRealizationPullbackFrames
import all WeilConjectures.AlgebraicGeometry.ProjectiveBundleRealizationPullbackTargetFrame
import all WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientPulledChartNormalization

/-! # Cross-tensor relations for realization base change
Source: Stacks Project, Tags 01NQ, 01NR and 01OB.
(blueprint: lem-pur-projective-bundle-realization-pullback-cross-tensor).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
open Scheme.Modules CategoryTheory.MonoidalCategory
attribute [local irreducible] tensorPullback projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction
  Scheme.GradedAlgebraData.relProjHom Scheme.GradedAlgebraData.relProjι
  Scheme.GradedAlgebraData.relProj
  Scheme.GradedAlgebraData.PullbackData.relProjComparison
  Proj Proj.map Proj.twist

set_option maxHeartbeats 800000 in
-- Linear maps on a pulled line are compared using its specified free section.
private theorem cross_from_chart_map {T Y : Scheme.{u}} (j : Y ⟶ T)
    [IsOpenImmersion j] {M P Q : T.Modules} (q : M ⟶ P) (q' : M ⟶ Q)
    (v : (tensorPullback j).obj P ⟶ (tensorPullback j).obj Q)
    (V : T.Opens) (hV : V ≤ j.opensRange) (s : Γ(P, V)) (hs : IsFreeGenerator s)
    (m n : Γ(M, V))
    (hm : v.app (j ⁻¹ᵁ V) (tensorPullbackSection j P V (q.app V m)) =
      tensorPullbackSection j Q V (q'.app V m))
    (hn : v.app (j ⁻¹ᵁ V) (tensorPullbackSection j P V (q.app V n)) =
      tensorPullbackSection j Q V (q'.app V n)) :
    tmulSection (q.app V m) (q'.app V n) =
      tmulSection (q.app V n) (q'.app V m) := by
  let a := hs.coeff (q.app V m)
  let c := hs.coeff (q.app V n)
  have ha : a • s = q.app V m := hs.coeff_smul _
  have hc : c • s = q.app V n := hs.coeff_smul _
  have hac : a • q.app V n = c • q.app V m := by
    rw [← ha, ← hc, smul_comm]
  have hac' : a • q'.app V n = c • q'.app V m := by
    apply ProjectiveBundleQuotientGeometry.tensor_section_injective j Q V hV
    rw [ProjectiveBundleQuotientGeometry.tensor_section_smul,
      ProjectiveBundleQuotientGeometry.tensor_section_smul, ← hm, ← hn,
      ← Hom.app_smul, ← Hom.app_smul,
      ← ProjectiveBundleQuotientGeometry.tensor_section_smul,
      ← ProjectiveBundleQuotientGeometry.tensor_section_smul, hac]
  rw [← ha, ← hc, smul_tmulSection, smul_tmulSection,
    ← tmulSection_smul, ← tmulSection_smul, hac']


set_option maxHeartbeats 2000000 in
-- The comparison retains both normalized pullback coherence chains.
/-- The cross-tensor identity for the two normalized realization pullback quotients.

Source: Stacks Project, Tags 01NQ, 01NR and 01OB.
(blueprint: lem-pur-projective-bundle-realization-pullback-cross-tensor).

Proof: use the explicit quotient-frame cover to obtain a free source section locally.
On each affine pair, conjugate the concrete degree-one homogeneous-fraction map by the
realization charts. The chart-image lemma says that this linear map sends each pulled source
quotient image to its normalized target quotient image. Extract coefficients with the local
source free generator; linearity transfers scalar relations to the target images. Open
immersion pullback detects equality, so the cross relation follows for pulled affine base
sections. Sheaf separatedness glues it. Transport to a single pullback along the composite;
extension of scalars on stalks and bilinearity extend the relation to every local section.
Transport back by the specified pullback-composition isomorphism to obtain exactly q and q'. -/
theorem projectiveBundleRealizationPullback_cross_tensor
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
    ∀ (V : D'.A.data.relProj.Opens) (m n : Γ(M, V)),
      Scheme.Modules.tmulSection (q.app V m) (q'.app V n) =
        Scheme.Modules.tmulSection (q.app V n) (q'.app V m) := by
  classical
  intro M q q'
  let r := b.relProjComparison
  let p := D.A.data.relProjHom
  let f := r ≫ p
  let P := (tensorPullback r).obj D.L
  let c := (projectiveBundlePullbackComp r p).app F
  let q₀ := c.inv ≫ q
  let q₁ := c.inv ≫ q'
  let I := Σ a : Scheme.GradedAlgebraData.PullbackData.Pairs g, Γ(F, a.1.2.1)
  let U : I → D'.A.data.relProj.Opens := fun i ↦
    D'.A.data.relProjι i.1.1.1 ''ᵁ Proj.basicOpen (D'.A.data.grading i.1.1.1)
      (b.map i.1.2 (D.A.sectionEquiv i.1.1.2 (SymmetricAlgebra.ι _ _ i.2)))
  obtain ⟨hU, hcover, hs, ht⟩ :=
    exists_projectiveBundleRealizationPullbackAtlas_frames D D' g e b hb
  have H : ∀ (V : D'.A.data.relProj.Opens)
      (m n : Γ((tensorPullback f).obj F, V)),
      tmulSection (q₀.app V m) (q₁.app V n) =
        tmulSection (q₀.app V n) (q₁.app V m) := by
    apply tensorPullback_cross_tensor_of_generators f F q₀ q₁
    intro W m n
    apply (P ⊗ D'.L).isSheaf.section_ext
    intro z hz
    have hz' : g (D'.A.data.relProjHom z) ∈ W.1 := by
      change (r ≫ p) z ∈ W.1 at hz
      have he := congrArg (fun t ↦ t z) b.isPullback.w
      exact he ▸ hz
    obtain ⟨W'₀, hW', hzW', hW'g⟩ := exists_isAffineOpen_mem_and_subset
      (x := D'.A.data.relProjHom z) (U := g ⁻¹ᵁ W.1) hz'
    let W' : B'.affineOpens := ⟨W'₀, hW'⟩
    obtain ⟨v, hv⟩ := projectiveBundleRealizationPullback_chart_images D D' g e b hb
      W W' hW'g
    obtain ⟨i, hzi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcover.ge (Set.mem_univ z))
    let V := (f ⁻¹ᵁ W.1) ⊓ (D'.A.data.relProjHom ⁻¹ᵁ W'.1) ⊓ U i
    have hV : V ≤ f ⁻¹ᵁ W.1 := inf_le_left.trans inf_le_left
    have hT : V ≤ D'.A.data.relProjHom ⁻¹ᵁ W'.1 := inf_le_left.trans inf_le_right
    have hi : V ≤ U i := inf_le_right
    refine ⟨V, hV, ⟨⟨hz, hzW'⟩, hzi⟩, ?_⟩
    rw [tmulSection_map, tmulSection_map, ← Hom.app_presheaf_map,
      ← Hom.app_presheaf_map, ← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
    have hS : V ≤ r ⁻¹ᵁ (p ⁻¹ᵁ W.1) := hV
    let m' := M.presheaf.map (homOfLE hS).op
      (projectiveBundlePullbackSection r (projectiveBundlePullbackSection p m))
    let n' := M.presheaf.map (homOfLE hS).op
      (projectiveBundlePullbackSection r (projectiveBundlePullbackSection p n))
    have hcm : c.inv.app V (((tensorPullback f).obj F).presheaf.map
        (homOfLE hV).op (projectiveBundlePullbackSection f m)) = m' := by
      have he := section_comp_restrict_inv r p le_rfl hS m
      simp only [Scheme.Modules.presheaf_map_id_apply] at he
      dsimp only [c, f, m', M, Iso.app]
      exact he
    have hcn : c.inv.app V (((tensorPullback f).obj F).presheaf.map
        (homOfLE hV).op (projectiveBundlePullbackSection f n)) = n' := by
      have he := section_comp_restrict_inv r p le_rfl hS n
      simp only [Scheme.Modules.presheaf_map_id_apply] at he
      dsimp only [c, f, n', M, Iso.app]
      exact he
    dsimp only [q₀, q₁]
    simp only [Hom.comp_app, ConcreteCategory.comp_apply]
    rw [hcm, hcn]
    apply cross_from_chart_map (D'.A.data.relProjι W') q q' v V
      (by rw [← D'.A.data.relProjHom_preimage]; exact hT) _ ((hs i).map hi) m' n'
    · exact hv V hS hT m
    · exact hv V hS hT n
  intro V m n
  have hm : c.inv.app V (c.hom.app V m) = m := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id]
    rfl
  have hn : c.inv.app V (c.hom.app V n) = n := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id]
    rfl
  have hh := H V (c.hom.app V m) (c.hom.app V n)
  dsimp only [q₀, q₁] at hh
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, hm, hn] at hh
  exact hh

end AlgebraicGeometry
