/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleSymmetricAlgebraIso

/-! # Epimorphy of the quotient of an arbitrary normalized projective-bundle realization
Source: Stacks Project, Constructions, Tags 01OB and 01O4.
The local argument follows SymmetricProjNormalizedQuotientEpi, transporting its generators
by the realization section equivalence.
(blueprint: lem-pur-projective-bundle-quotient-epi). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
namespace AlgebraicGeometry
open Scheme.Modules
attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  projectiveBundlePullbackAdjunction projectiveBundlePullbackSection
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι

private theorem projective_bundle_unit_section {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : Y.Modules) (U : Y.Opens) (m : Γ(F, U)) :
    ((projectiveBundlePullbackAdjunction g).unit.app F).app U m =
      projectiveBundlePullbackSection g m := by
  unfold projectiveBundlePullbackSection
  rfl

private theorem tensor_unit_injective {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (V : Y.Opens) (hV : V ≤ j.opensRange) :
    Function.Injective (((projectiveBundlePullbackAdjunction j).unit.app M).app V) := by
  let a := projectiveBundlePullbackAdjunction j
  let b := pullbackPushforwardAdjunction j
  have h := a.unit_leftAdjointUniq_hom_app b M
  have hi := (bijective_pullbackUnit_app_of_isOpenImmersion j M hV).injective
  intro s t hst
  apply hi
  have hs := congrArg (fun f ↦ f.app V s) h
  have ht := congrArg (fun f ↦ f.app V t) h
  change _ = (pullbackUnit j M).app V s at hs
  change _ = (pullbackUnit j M).app V t at ht
  rw [← hs, ← ht]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app]
  exact congrArg _ hst

private theorem zero_of_tensor_open_cover {X : Scheme.{u}} {I : Type u}
    (Y : I → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hj : ⨆ i, (j i).opensRange = ⊤) {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ i, (tensorPullback (j i)).map f = 0) : f = 0 := by
  apply hom_ext
  intro V
  ext s
  change f.app V s = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i ↦ V ⊓ (j i).opensRange) V (fun _ ↦ homOfLE inf_le_left)
    (fun x hx ↦ ?_) _ 0 (fun i ↦ ?_)
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hj.ge (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · rw [map_zero, ← Hom.app_presheaf_map]
    let W := V ⊓ (j i).opensRange
    let t : Γ(M, W) := M.presheaf.map (homOfLE inf_le_left).op s
    apply tensor_unit_injective (j i) N W inf_le_right
    have h := congrArg (fun k ↦ k.app W t)
      ((projectiveBundlePullbackAdjunction (j i)).unit.naturality f)
    change ((projectiveBundlePullbackAdjunction (j i)).unit.app N).app W (f.app W t) =
      ((tensorPullback (j i)).map f).app ((j i) ⁻¹ᵁ W)
        (((projectiveBundlePullbackAdjunction (j i)).unit.app M).app W t) at h
    change ((projectiveBundlePullbackAdjunction (j i)).unit.app N).app W (f.app W t) =
      ((projectiveBundlePullbackAdjunction (j i)).unit.app N).app W 0
    rw [map_zero, h, hf i]
    rfl

private theorem zero_of_twist_generators {R B : Type u} [CommRing R]
    [SetLike B R] [AddSubgroupClass B R] (𝒜 : ℕ → B) [GradedRing 𝒜]
    {I : Type u} (a : I → R) (ha : ∀ i, a i ∈ 𝒜 1)
    (hcover : ⨆ i, Proj.basicOpen 𝒜 (a i) = ⊤)
    {N : (Proj 𝒜).Modules} (g : Proj.twist 𝒜 1 ⟶ N)
    (hg : ∀ i, Proj.unitToTwist (ha i) ≫ g = 0) : g = 0 := by
  apply hom_ext
  intro V
  ext t
  change g.app V t = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i ↦ V ⊓ Proj.basicOpen 𝒜 (a i)) V (fun _ ↦ homOfLE inf_le_left)
    (fun x hx ↦ ?_) _ 0 (fun i ↦ ?_)
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · rw [map_zero, ← Hom.app_presheaf_map]
    let W := V ⊓ Proj.basicOpen 𝒜 (a i)
    obtain ⟨r, hr⟩ := (Proj.bijective_unitToTwist_app (ha i)
      (V := W) inf_le_right).surjective
      ((Proj.twist 𝒜 1).presheaf.map (homOfLE inf_le_left).op t)
    rw [← hr]
    exact congrArg (fun k ↦ k.app W r) (hg i)

/-- The normalized tautological quotient of any symmetric-algebra realization is epic.
Source: Stacks Project, Tags 01OB and 01O4.
Proof: its affine twist charts identify quotient sections with degree-one inclusion sections.
Their standard opens cover, since the symmetric algebra is generated by scalars and inclusion
vectors. On each such open the inclusion section freely generates the twist, so any map
annihilating the quotient is zero there. Tensor pullback to the affine chart cover detects
zero morphisms by the sheaf axiom and injectivity of the open-immersion pullback unit.
Cancellation against zero therefore proves epimorphy.
(blueprint: lem-pur-projective-bundle-quotient-epi). -/
theorem projectiveBundleQuotient_epi
    {S : Scheme.{u}} {F : S.Modules} (D : ProjectiveBundleRealization S F) :
    Epi D.quotient := by
  classical
  let A := D.A.data
  let p := A.relProjHom
  let L := D.L
  let adj := projectiveBundlePullbackAdjunction p
  let σ := adj.homEquiv F L D.quotient
  apply Preadditive.epi_of_cancel_zero
  intro N f hf
  have hσf : σ ≫ (pushforward p).map f = 0 := by
    have h := congrArg (adj.homEquiv F N) hf
    rw [adj.homEquiv_naturality_right] at h
    exact h.trans (by rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero])
  apply zero_of_tensor_open_cover
    (fun U : S.affineOpens ↦ Proj (A.grading U)) A.relProjι A.iSup_opensRange_relProjι f
  intro U
  let : GradedAlgebra (A.grading U) := A.gradedAlgebra U
  let j := A.relProjι U
  let g := (D.twists.chart U).inv ≫ (tensorPullback j).map f
  have htop : j ⁻¹ᵁ (p ⁻¹ᵁ U.1) = ⊤ := by
    rw [A.relProjHom_preimage U]
    exact j.preimage_opensRange
  have hgen (m : F.val.obj (op U.1))
      (hm : D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ m) ∈ A.grading U 1) :
      Proj.unitToTwist hm ≫ g = 0 := by
    apply unit_hom_ext
    change g.app ⊤ ((Proj.unitToTwist hm).app ⊤ (1 : Γ(Proj (A.grading U), ⊤))) = 0
    have hn := D.quotient_generator U m hm
    have hz : f.app (p ⁻¹ᵁ U.1) (σ.app U.1 m) = 0 := by
      exact congrArg (fun k ↦ k.app U.1 m) hσf
    have hnat := congrArg (fun k ↦ k.app (p ⁻¹ᵁ U.1) (σ.app U.1 m))
      ((projectiveBundlePullbackAdjunction j).unit.naturality f)
    simp only [Functor.id_map, Functor.comp_map, Hom.comp_app,
      ConcreteCategory.comp_apply, pushforward_map_app, projective_bundle_unit_section] at hnat
    change projectiveBundlePullbackSection j (M := N)
        (f.app (p ⁻¹ᵁ U.1) (σ.app U.1 m)) =
      ((tensorPullback j).map f).app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
        (projectiveBundlePullbackSection j (M := L) (σ.app U.1 m)) at hnat
    rw [hz, ← projective_bundle_unit_section, map_zero] at hnat
    have he : g.app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
        ((D.twists.chart U).hom.app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
          (projectiveBundlePullbackSection j (M := L) (σ.app U.1 m))) = 0 := by
      change (((D.twists.chart U).hom ≫ g).app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))) _ = 0
      simp only [g, Iso.hom_inv_id_assoc]
      exact hnat.symm
    rw [hn] at he
    change g.app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
      ((Proj.unitToTwist hm).app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
        (1 : Γ(Proj (A.grading U), j ⁻¹ᵁ (p ⁻¹ᵁ U.1)))) = 0 at he
    rw [htop] at he
    exact he
  have hm (m : F.val.obj (op U.1)) :
      D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ m) ∈ A.grading U 1 := by
    apply (D.A.sectionEquiv_grade U 1 _).mp
    rw [projectiveBundleSymmetricDegree_eq, pow_one]
    exact LinearMap.mem_range_self _ m
  have hg : g = 0 := zero_of_twist_generators (A.grading U)
    (fun m ↦ D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ m)) hm
    (realization_chart_cover D.A U hm) g
    (fun m ↦ hgen m (hm m))
  have h := congrArg ((D.twists.chart U).hom ≫ ·) hg
  simpa only [g, Iso.hom_inv_id_assoc, comp_zero] using h

end AlgebraicGeometry
