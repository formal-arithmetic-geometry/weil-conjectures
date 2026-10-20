/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Zero
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Rank-zero projective bundles

The sole normalized coordinate is a global free generator on each frame open.
Source: Stacks Project, Tag 01OE.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundleTensorPullbackIso projectiveBundlePullbackId projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

private theorem isIso_of_global_generator {X : Scheme.{u}} {M : X.Modules}
    (s : Scheme.Modules.unit X ⟶ M)
    (hs : Scheme.Modules.IsFreeGenerator
      (Scheme.Modules.Hom.app s ⊤ (1 : Γ(X, ⊤)))) : IsIso s := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  have heq : (fun r : Γ(X, U) ↦ s.app U r) =
      fun r : Γ(X, U) ↦ r • M.presheaf.map (homOfLE le_top).op
        (s.app ⊤ (1 : Γ(X, ⊤))) := by
    funext r
    rw [← Scheme.Modules.Hom.app_presheaf_map, ← Scheme.Modules.Hom.app_smul]
    congr 1
    symm
    change r * X.presheaf.map _ 1 = r
    simp
  change Function.Bijective (fun r : Γ(X, U) ↦ s.app U r)
  rw [heq]
  exact hs U le_top

private theorem isIso_of_generator_on_top {X : Scheme.{u}} {M : X.Modules}
    (s : Scheme.Modules.unit X ⟶ M) (W : X.Opens) (hW : W = ⊤)
    (hs : Scheme.Modules.IsFreeGenerator (M.presheaf.map
      (homOfLE (le_top : W ≤ ⊤)).op
      (Scheme.Modules.Hom.app s ⊤ (1 : Γ(X, ⊤))))) : IsIso s := by
  subst W
  simp only [Scheme.Modules.presheaf_map_id_apply] at hs
  exact isIso_of_global_generator s hs

private theorem free_inclusion_isIso (X : Scheme.{u}) (I : Type u) [Unique I]
    (i : I) : IsIso (SheafOfModules.ιFree (R := X.ringCatSheaf) i) := by
  have hi : SheafOfModules.ιFree (R := X.ringCatSheaf) i =
      (SheafOfModules.freeUniqueIso (R := X.ringCatSheaf) I).inv := by
    change Sigma.ι (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf) i = _
    rw [SheafOfModules.freeUniqueIso, coproductUniqueIso_inv]
    congr 1
    exact Subsingleton.elim _ _
  rw [hi]
  infer_instance

private theorem isIso_of_unique_chart {J : Type u} [Unique J]
    {X S : Scheme.{u}} (φ : X ⟶ ℙ(J; S)) {M : X.Modules}
    (s : Scheme.Modules.unit X ⟶ M) (i : J)
    (hs : Scheme.Modules.IsFreeGenerator (M.presheaf.map
      (homOfLE (le_top : φ ⁻¹ᵁ ProjectiveSpace.standardOpen J S i ≤ ⊤)).op
      (Scheme.Modules.Hom.app s ⊤ (1 : Γ(X, ⊤))))) : IsIso s := by
  have hstd : ProjectiveSpace.standardOpen J S i = ⊤ := by
    rw [show i = default from Subsingleton.elim _ _]
    exact (iSup_unique (ProjectiveSpace.standardOpen J S)).symm.trans
      (ProjectiveSpace.iSup_standardOpen J S)
  have hW : φ ⁻¹ᵁ ProjectiveSpace.standardOpen J S i = ⊤ := by
    rw [hstd]
    exact Scheme.Hom.preimage_top φ
  exact isIso_of_generator_on_top s _ hW hs

private theorem quotient_isIso_on_frame_zero
    {B : Scheme.{u}} {F : B.Modules} (D : ProjectiveBundleRealization B F)
    (U : B.Opens) (e : B.ModuleFrame F U (0 + 1))
    (C : ProjectiveBundleFrameChart D 0 U e) :
    IsIso ((Scheme.Modules.tensorPullback (D.A.data.relProjHom ⁻¹ᵁ U).ι).map D.quotient) := by
  classical
  let : Unique (ULift.{u} (Fin (0 + 1))) :=
    inferInstanceAs (Unique (ULift.{u} (Fin 1)))
  let i : ULift.{u} (Fin (0 + 1)) := default
  have hs : IsIso (projectiveBundleFrameSection D 0 U e i) :=
    isIso_of_unique_chart (C.relativeChart.hom ≫ C.polynomialChart.hom) _ i (C.generator i)
  have hi : IsIso (SheafOfModules.ιFree
      (R := U.toScheme.ringCatSheaf) i) := free_inclusion_isIso U.toScheme _ i
  have hv : IsIso (projectiveBundleFrameVector D 0 U e i) :=
    projectiveBundleFrameVector_isIso D 0 U e i
  rw [projectiveBundleFrameSection_eq] at hs
  exact IsIso.of_isIso_comp_left (projectiveBundleFrameVector D 0 U e i) _

/-- Rank-zero quotient and structural isomorphism, obtained from the one-coordinate frame chart.
Source: Stacks, Tag 01OE; rank-zero clause of the projective-bundle tautological geometry.
(blueprint: lem-pur-projective-bundle-rank-zero).

Proof: choose an affine frame cover of the rank-one module. On every frame open the
one-coordinate projective space is isomorphic to the base, and the frame quotient is
the unique coordinate generator, hence an isomorphism. The quotient isomorphisms agree
on overlaps because they send the same normalized frame section to the same coordinate
section. They glue, and the structural isomorphism follows by target locality. -/
theorem exists_projectiveBundleRankZero
    {B : Scheme.{u}} {F : B.Modules} [F.IsFiniteLocallyFreeOfRank (0 + 1)]
    (D : ProjectiveBundleRealization B F)
    (frame : ∀ (U : B.Opens) (e : B.ModuleFrame F U (0 + 1)),
      ProjectiveBundleFrameChart D 0 U e) :
    ∃ _qiso : D.L ≅ (Scheme.Modules.tensorPullback D.A.data.relProjHom).obj F,
      IsIso D.A.data.relProjHom := by
  classical
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := 0 + 1)
  let frames (i : I) : B.ModuleFrame F (U i) (0 + 1) :=
    (projectiveBundleTensorPullbackIso (U i).ι).app F ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app F).symm ≪≫ (e i).some
  have hq : IsIso D.quotient := by
    refine Scheme.Modules.isIso_of_isIso_pullback_map
      (fun i ↦ (D.A.data.relProjHom ⁻¹ᵁ U i).ι) ?_ D.quotient ?_
    · intro x
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (hU.ge (show D.A.data.relProjHom x ∈ (⊤ : B.Opens) from trivial))
      exact ⟨i, ⟨x, hi⟩, rfl⟩
    · intro i
      have ht := quotient_isIso_on_frame_zero D (U i) (frames i) (frame (U i) (frames i))
      let α := projectiveBundleTensorPullbackIso (D.A.data.relProjHom ⁻¹ᵁ U i).ι
      have heq : (Scheme.Modules.pullback (D.A.data.relProjHom ⁻¹ᵁ U i).ι).map D.quotient =
          α.inv.app _ ≫ (Scheme.Modules.tensorPullback
            (D.A.data.relProjHom ⁻¹ᵁ U i).ι).map D.quotient ≫ α.hom.app _ := by
        rw [α.hom.naturality, ← Category.assoc, α.inv_hom_id_app, Category.id_comp]
      rw [heq]
      infer_instance
  refine ⟨(asIso D.quotient).symm, ?_⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) U hU
  intro i
  let C := frame (U i) (frames i)
  rw [← C.relativeChart_over, ← C.polynomialChart_over]
  change IsIso (C.relativeChart.hom ≫ C.polynomialChart.hom ≫
    (ℙ(ULift.{u} (Fin (0 + 1)); (U i).toScheme) ↘ (U i).toScheme))
  have hproj : IsIso
      (ℙ(ULift.{u} (Fin 1); (U i).toScheme) ↘ (U i).toScheme) := inferInstance
  let hp0 : IsIso
      (ℙ(ULift.{u} (Fin (0 + 1)); (U i).toScheme) ↘ (U i).toScheme) := by
    simpa only [Nat.zero_add] using hproj
  infer_instance
end AlgebraicGeometry
