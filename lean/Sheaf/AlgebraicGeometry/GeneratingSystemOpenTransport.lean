/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J9
-/
module

public import Sheaf.AlgebraicGeometry.PrescribedPointSystemData
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-!
# Transporting a generating linear system to an open subscheme

Source: Stacks Project, Constructions, Tags 01NE and 01NF; Schemes, Tag 02V0.
(blueprint: lem-zl-generating-system-open-transport).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules MonoidalCategory

noncomputable section

attribute [local irreducible] tensorPullback prescribedPointRestrictedFamily

private noncomputable def tensorComparison {A B : Scheme.{u}} (g : A ⟶ B) :
    tensorPullback g ≅ Scheme.Modules.pullback g :=
  (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)

private theorem tensorUnit_eq {A B : Scheme.{u}} (g : A ⟶ B) (M : B.Modules) :
    tensorSectionsUnit g M =
      (show Γ(M, ⊤) ⟶ Γ((tensorPullback g).obj M, ⊤) from
        ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M).app ⊤) := by
  unfold tensorSectionsUnit
  have hi : (homOfLE g.preimage_top.ge).op = 𝟙 (op (⊤ : A.Opens)) := rfl
  erw [hi, ((tensorPullback g).obj M).presheaf.map_id, Category.comp_id]

private theorem comparison_unit {A B : Scheme.{u}} (g : A ⟶ B) (M : B.Modules)
    (v : Γ(M, ⊤)) :
    ((tensorComparison g).app M).hom.app ⊤ (tensorSectionsUnit g M v) = pullbackΓ g M v := by
  rw [tensorUnit_eq, pullbackΓ_def]
  exact congrArg (fun h ↦ h.app ⊤ v)
    ((Classical.choose (exists_tensorPullbackAdjunction g)).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction g) M)

private theorem comparison_inv_unit {A B : Scheme.{u}} (g : A ⟶ B) (M : B.Modules)
    (v : Γ(M, ⊤)) :
    ((tensorComparison g).app M).inv.app ⊤ (pullbackΓ g M v) = tensorSectionsUnit g M v := by
  rw [← comparison_unit g M v]
  change (((tensorComparison g).app M).hom ≫ ((tensorComparison g).app M).inv).app ⊤ _ = _
  rw [Iso.hom_inv_id]
  rfl

private theorem section_ext_top {A : Scheme.{u}} {M : A.Modules} (s t : M.sections)
    (h : s.val (op ⊤) = t.val (op ⊤)) : s = t := by
  apply Subtype.ext
  funext U
  have hs := s.property (homOfLE (le_top : U.unop ≤ ⊤)).op
  have ht := t.property (homOfLE (le_top : U.unop ≤ ⊤)).op
  exact hs.symm.trans ((congrArg (M.presheaf.map
    (homOfLE (le_top : U.unop ≤ ⊤)).op) h).trans ht)

private theorem family_top {A : Scheme.{u}} (M : A.Modules) {I : Type u}
    (s : I → Γ(M, ⊤)) (i : I) : (bertiniSectionFamily M s i).val (op ⊤) = s i := by
  exact (homOfGlobalSection_app_one M (s i) ⊤).trans (presheaf_map_id_apply _ _)

private theorem pullback_free_eval {A B : Scheme.{u}} (g : A ⟶ B) (M : B.Modules)
    {I : Type u} (s : I → M.sections) (i : I) :
    ((((Scheme.Modules.pullback g).obj M).freeHomEquiv
      ((pullbackFreeIso g I).inv ≫ (Scheme.Modules.pullback g).map
        (M.freeHomEquiv.symm s)) i).val (op ⊤)) =
      pullbackΓ g M ((s i).val (op ⊤)) := by
  change Hom.app (SheafOfModules.ιFree i ≫ (pullbackFreeIso g I).inv ≫
    (Scheme.Modules.pullback g).map (M.freeHomEquiv.symm s)) ⊤ (1 : Γ(A, ⊤)) = _
  rw [← Category.assoc, ιFree_pullbackFreeIso_inv, Category.assoc, ← Functor.map_comp]
  rw [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [show (pullbackObjUnitIso g).inv.app ⊤ (1 : Γ(A, ⊤)) =
    pullbackΓ g (𝟙_ B.Modules) (1 : Γ(B, ⊤)) by
      rw [pullbackΓ_apply]
      exact (pullbackSection_one_eq g).symm]
  erw [pullbackΓ_naturality]
  congr 1
  exact congrArg (fun t : I → M.sections ↦ (t i).val (op ⊤))
    (M.freeHomEquiv.apply_symm_apply s)

private theorem classifying_pullback_iso
    {A B C : Scheme.{u}} (a : A ⟶ B) (g : B ⟶ C)
    (M : B.Modules) (Q : A.Modules) [M.IsInvertible] [Q.IsInvertible]
    (E : (Scheme.Modules.pullback a).obj M ≅ Q)
    (I : Type u) [Finite I] (s : I → M.sections) (t : I → Q.sections)
    (hs : Epi (M.freeHomEquiv.symm s)) (ht : Epi (Q.freeHomEquiv.symm t))
    (hvalue : ∀ i, E.hom.app ⊤ (pullbackΓ a M ((s i).val (op ⊤))) =
      (t i).val (op ⊤)) :
    a ≫ ProjectiveSpace.homOfGeneratingSections I g M s hs =
      ProjectiveSpace.homOfGeneratingSections I (a ≫ g) Q t ht := by
  classical
  let ψ := ProjectiveSpace.integralHomOfGeneratingSections I M s hs
  let T := ProjectiveSpace.twist I (Spec (CommRingCat.of (ULift.{u} ℤ))) 1
  obtain ⟨e, he⟩ := ProjectiveSpace.integralHomOfGeneratingSections_spec I M s hs
  let ε : (Scheme.Modules.pullback ψ).obj T ≅ M :=
    ((tensorComparison ψ).app T).symm ≪≫ e
  have hε (i : I) : ε.hom.app ⊤
      (pullbackΓ ψ T (ProjectiveSpace.twistOneSection I _ i)) = (s i).val (op ⊤) := by
    dsimp only [ε, Iso.trans_hom, Iso.symm_hom]
    rw [Hom.comp_app, ConcreteCategory.comp_apply]
    erw [comparison_inv_unit, tensorUnit_eq]
    exact he i
  let F : (tensorPullback (a ≫ ψ)).obj T ≅ Q :=
    (tensorComparison (a ≫ ψ)).app T ≪≫
      (pullbackCompOfEq a ψ (a ≫ ψ) rfl T).symm ≪≫
      (Scheme.Modules.pullback a).mapIso ε ≪≫ E
  have hF (i : I) : F.hom.app ⊤
      (tensorSectionsUnit (a ≫ ψ) T (ProjectiveSpace.twistOneSection I _ i)) =
        (t i).val (op ⊤) := by
    simp only [F, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Hom.comp_app, ConcreteCategory.comp_apply]
    rw [comparison_unit, pullbackCompOfEq_inv_app_pullbackΓ,
      pullbackΓ_naturality, hε, hvalue]
  have hψ : a ≫ ψ = ProjectiveSpace.integralHomOfGeneratingSections I Q t ht := by
    apply (Classical.choose_spec
      (ProjectiveSpace.generatingSections_integralHom_exists I Q t ht)).2
    refine ⟨F, ?_⟩
    intro i
    have hi := hF i
    rw [tensorUnit_eq] at hi
    exact hi
  apply (ProjectiveSpace.homOfGeneratingSections_spec I (a ≫ g) Q t ht).2.2
  · rw [Category.assoc,
      (ProjectiveSpace.homOfGeneratingSections_spec I g M s hs).1]
  · rw [Category.assoc,
      (ProjectiveSpace.homOfGeneratingSections_spec I g M s hs).2.1,
      ← Category.assoc, hψ]

/-- Pulling back a generating system through an open immersion and a module isomorphism
preserves generation and the immersion defined by that system. The new sections are
specified by their actual global values, using the tensor-pullback unit.

Source: Stacks Project, Constructions, Tags 01NE and 01NF, classification by an
invertible module with generating sections; Schemes, Tag 02V0, composition of immersions.
(blueprint: lem-zl-generating-system-open-transport).

Proof: Factor `(j^-1 V).ι ≫ j` through `V.ι`. The factor is an open immersion.
Pull back the epimorphism classified by `t`; pullback preserves epimorphisms since it
is a left adjoint. Identify the pullback of the free module with the free module on
the same indices. The canonical composition comparison, the comparison between
ordinary and tensor pullback by uniqueness of left adjoints, and the pullback of `e`
give an isomorphism of the resulting target with the displayed target. Naturality
of the adjunction units shows, on global sections, that its generators are exactly
the displayed restricted family. This proves the new epimorphism. The same
section-preserving isomorphism and the uniqueness in the projective-space
classification identify the new classifying morphism with the old one composed
with that open immersion. Composition preserves immersions, giving the conclusion.
No nonemptiness assumption on the open or on the finite index type is used.
-/
theorem generatingSystem_open_transport
    {B X Y : Scheme.{u}} (f : Y ⟶ B) (j : X ⟶ Y) [IsOpenImmersion j]
    (V : Y.Opens) (M P : Y.Modules) [M.IsInvertible] [P.IsInvertible]
    (e : M ≅ P) (I : Type u) [Finite I]
    (s : I → M.sections) (t : I → ((Scheme.Modules.pullback V.ι).obj M).sections)
    (hvalue : ∀ a : I, (t a).val (op ⊤) = pullbackΓ V.ι M ((s a).val (op ⊤)))
    (ht : Epi ((((Scheme.Modules.pullback V.ι).obj M).freeHomEquiv).symm t))
    (himm : IsImmersion (@ProjectiveSpace.homOfGeneratingSections I inferInstance
      V.toScheme B (V.ι ≫ f) ((Scheme.Modules.pullback V.ι).obj M) inferInstance t ht))
    (hP : ((tensorPullback ((j ⁻¹ᵁ V).ι ≫ j)).obj P).IsInvertible) :
    let s' : I → Γ(P, ⊤) := fun a ↦ e.hom.app ⊤ ((s a).val (op ⊤))
    ∃ ht' : Epi ((((tensorPullback ((j ⁻¹ᵁ V).ι ≫ j)).obj P).freeHomEquiv).symm
        (prescribedPointRestrictedFamily P j (j ⁻¹ᵁ V) s')),
      IsImmersion (@ProjectiveSpace.homOfGeneratingSections I inferInstance
        (j ⁻¹ᵁ V).toScheme B ((j ⁻¹ᵁ V).ι ≫ j ≫ f)
        ((tensorPullback ((j ⁻¹ᵁ V).ι ≫ j)).obj P) hP
        (prescribedPointRestrictedFamily P j (j ⁻¹ᵁ V) s') ht') := by
  classical
  dsimp only
  let U := j ⁻¹ᵁ V
  let a := j.resLE V U le_rfl
  have ha : a ≫ V.ι = U.ι ≫ j := j.resLE_comp_ι le_rfl
  have : IsOpenImmersion a := by
    have : IsOpenImmersion (a ≫ V.ι) := by rw [ha]; infer_instance
    exact IsOpenImmersion.of_comp a V.ι
  let Q := (Scheme.Modules.pullback V.ι).obj M
  let R := (tensorPullback (U.ι ≫ j)).obj P
  let E : (Scheme.Modules.pullback a).obj Q ≅ R :=
    pullbackCompOfEq a V.ι (U.ι ≫ j) ha M ≪≫
      (Scheme.Modules.pullback (U.ι ≫ j)).mapIso e ≪≫
      ((tensorComparison (U.ι ≫ j)).app P).symm
  let F := (pullbackFreeIso a I).inv ≫
    (Scheme.Modules.pullback a).map (Q.freeHomEquiv.symm t)
  have : Epi F := by
    let : Epi (Q.freeHomEquiv.symm t) := ht
    dsimp only [F]
    infer_instance
  let t' := R.freeHomEquiv (F ≫ E.hom)
  have ht' : Epi (R.freeHomEquiv.symm t') := by
    dsimp only [t']
    rw [Equiv.symm_apply_apply]
    infer_instance
  have htop (i : I) : (t' i).val (op ⊤) = tensorSectionsUnit (U.ι ≫ j) P
      (e.hom.app ⊤ ((s i).val (op ⊤))) := by
    change E.hom.app ⊤ (((((Scheme.Modules.pullback a).obj Q).freeHomEquiv F) i).val
      (op ⊤)) = _
    rw [pullback_free_eval, hvalue]
    simp only [E, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Hom.comp_app, ConcreteCategory.comp_apply]
    rw [pullbackCompOfEq_hom_app_pullbackΓ, pullbackΓ_naturality, comparison_inv_unit]
  have ht'eq : t' = prescribedPointRestrictedFamily P j U
      (fun i ↦ e.hom.app ⊤ ((s i).val (op ⊤))) := by
    funext i
    apply section_ext_top
    rw [htop]
    unfold prescribedPointRestrictedFamily
    exact (family_top ((tensorPullback (U.ι ≫ j)).obj P)
      (fun i ↦ tensorSectionsUnit (U.ι ≫ j) P (e.hom.app ⊤ ((s i).val (op ⊤)))) i).symm
  let : R.IsInvertible := hP
  have hclass := classifying_pullback_iso a (V.ι ≫ f) Q R E I t t' ht ht'
    (fun i ↦ by
      change E.hom.app ⊤ (pullbackΓ a Q ((t i).val (op ⊤))) = _
      rw [htop, hvalue]
      simp only [E, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Hom.comp_app, ConcreteCategory.comp_apply]
      rw [pullbackCompOfEq_hom_app_pullbackΓ, pullbackΓ_naturality, comparison_inv_unit])
  have hnew : IsImmersion (ProjectiveSpace.homOfGeneratingSections I
      (a ≫ V.ι ≫ f) R t' ht') := by
    rw [← hclass]
    infer_instance
  have hbase : a ≫ V.ι ≫ f = U.ι ≫ j ≫ f := by
    rw [← Category.assoc, ha, Category.assoc]
  have result : ∃ h : Epi (R.freeHomEquiv.symm t'),
      IsImmersion (@ProjectiveSpace.homOfGeneratingSections I inferInstance
        U.toScheme B (U.ι ≫ j ≫ f) R hP t' h) :=
    ⟨ht', by simpa only [hbase] using hnew⟩
  simpa only [ht'eq] using result

end

end AlgebraicGeometry
