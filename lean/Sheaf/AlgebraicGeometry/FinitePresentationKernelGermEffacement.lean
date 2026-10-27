/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q20, Q3
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationCokernel

/-!
# Killing a kernel germ by a finitely presented quotient

Source: Stacks Project, Properties, Lemma 01PJ, injectivity paragraph
(blueprint: lem-weil-pbc-finite-presentation-kernel-germ-effacement).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

-- Cache the standard slice-site instances rather than rediscovering them for each image.
private noncomputable instance sliceHasSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} :=
  inferInstance

private noncomputable instance sliceHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} :=
  (sliceHasSheafify X U).isRightAdjoint

private noncomputable instance doubleSliceHasSheafify (X : Scheme.{u}) (U : X.Opens)
    (V : Over U) :
    HasSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{u} :=
  inferInstance

private noncomputable instance doubleSliceHasWeakSheafify (X : Scheme.{u}) (U : X.Opens)
    (V : Over U) :
    HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{u} :=
  (doubleSliceHasSheafify X U V).isRightAdjoint

private instance sliceLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance

private instance doubleSliceLocallyBijective (X : Scheme.{u}) (U : X.Opens) (V : Over U) :
    (((Opens.grothendieckTopology X).over U).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance

private noncomputable instance sliceAbelian (X : Scheme.{u}) (U : X.Opens) :
    Abelian (SheafOfModules.{u} (X.ringCatSheaf.over U)) := inferInstance

private theorem quasiCoherent_slice_image {X : Scheme.{u}} (U : X.Opens)
    {F G : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    [SheafOfModules.IsQuasicoherent.{u} F] [SheafOfModules.IsQuasicoherent.{u} G] (φ : F ⟶ G) :
    SheafOfModules.IsQuasicoherent.{u} (Abelian.image φ) := by
  have hcont₁ (V : TopologicalSpace.Opens ↥U) :
      (Over.post (X := V) U.overEquivalence.symm.functor).IsContinuous
        ((Opens.grothendieckTopology ↥U).over V)
        (((Opens.grothendieckTopology ↥X).over U).over
          (U.overEquivalence.inverse.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      (((U.overEquivalence.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp
        inferInstance).overPost V)
  have hcont₂ (V : Over U) :
      (Over.post (X := V) U.overEquivalence.symm.inverse).IsContinuous
        (((Opens.grothendieckTopology ↥X).over U).over V)
        ((Opens.grothendieckTopology ↥U).over (U.overEquivalence.functor.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      (((U.overEquivalence.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp
        inferInstance).overPost V)
  let T := (overEquiv U).functor
  have : SheafOfModules.IsQuasicoherent.{u} (T.obj F) :=
    @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u, u, u, u, u}
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) _ _ (fun V ↦ hcont₁ V) _ _ F _
  have : SheafOfModules.IsQuasicoherent.{u} (T.obj G) :=
    @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u, u, u, u, u}
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf) _ _ (fun V ↦ hcont₁ V) _ _ G _
  have hc := isQuasicoherent_cokernel (T.map φ)
  have : SheafOfModules.IsQuasicoherent.{u} (T.obj (Limits.cokernel φ)) :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (Limits.PreservesCokernel.iso T φ).symm hc
  have hk := isQuasicoherent_kernel (T.map (Limits.cokernel.π φ))
  have : SheafOfModules.IsQuasicoherent.{u} (T.obj (Abelian.image φ)) :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (Limits.PreservesKernel.iso T (Limits.cokernel.π φ)).symm hk
  have hback : SheafOfModules.IsQuasicoherent.{u}
      ((overEquiv U).inverse.obj (T.obj (Abelian.image φ))) :=
    @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u, u, u, u, u}
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) _ _
      (fun V ↦ hcont₂ V) _ _ (T.obj (Abelian.image φ)) _
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
    ((overEquiv U).unitIso.app (Abelian.image φ)).symm hback

private theorem finiteType_image_free_slice (X : Scheme.{u}) (U : X.Opens) (n : ℕ)
    {G : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    (φ : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)) ⟶ G) :
    SheafOfModules.IsFiniteType.{u} (Abelian.image φ) := by
  let g := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n))).ofEpi (Abelian.factorThruImage φ)
  let q := g.localGeneratorsData
  have : g.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
  apply SheafOfModules.IsFiniteType.mk
  refine ⟨q, ?_⟩
  refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := q) (fun i ↦ ?_)
  dsimp [q, SheafOfModules.GeneratingSections.localGeneratorsData]
  infer_instance

private noncomputable def section_on_open {X : Scheme.{u}} (E : X.Modules)
    (U : X.Opens) (s : E.val.obj (op U)) : (E.over U).sections :=
  (E.over U).val.sectionsMk
    (fun W ↦ E.val.map W.unop.hom.op s)
    (fun {W Z} f ↦ by
      change E.val.map f.unop.left.op (E.val.map W.unop.hom.op s) =
        E.val.map Z.unop.hom.op s
      exact (E.val.map_comp_apply W.unop.hom.op f.unop.left.op s).symm.trans
        (E.val.congr_map_apply (Subsingleton.elim _ _) s))

private theorem finiteType_section_carrier
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (E : X.Modules) [SheafOfModules.IsQuasicoherent.{u} E]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (s : E.val.obj (op U)) :
    ∃ (H : X.Modules) (h : H ⟶ E) (t : H.val.obj (op U)),
      SheafOfModules.IsQuasicoherent.{u} H ∧ SheafOfModules.IsFiniteType.{u} H ∧
        Mono h ∧ h.val.app (op U) t = s := by
  let φ : SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u} (Fin 1)) ⟶
      E.over U := (E.over U).freeHomEquiv.symm (fun _ ↦ section_on_open E U s)
  have : SheafOfModules.IsQuasicoherent.{u} (E.over U) := SheafOfModules.isQuasicoherent_over E U
  have hqc := quasiCoherent_slice_image U φ
  have hft := finiteType_image_free_slice X U 1 φ
  have : SheafOfModules.IsQuasicoherent.{u} (Abelian.image φ) := hqc
  have : SheafOfModules.IsFiniteType.{u} (Abelian.image φ) := hft
  obtain ⟨H, hHqc, hHft, h, hh, e, he⟩ :=
    exists_quasicoherent_finiteType_submodule_extension X U
      hU E (Abelian.image φ) (Abelian.image.ι φ)
  let τ := (Abelian.image φ).freeHomEquiv (Abelian.factorThruImage φ) ⟨0⟩
  let t := e.inv.val.app (op (Over.mk (𝟙 U)))
    (τ.val (op (Over.mk (𝟙 U))))
  refine ⟨H, h, t, hHqc, hHft, hh, ?_⟩
  have ht : (Abelian.image.ι φ).val.app (op (Over.mk (𝟙 U)))
      (τ.val (op (Over.mk (𝟙 U)))) = s := by
    have hsec := congrFun
      ((E.over U).freeHomEquiv.apply_symm_apply
        (fun _ : ULift.{u} (Fin 1) ↦ section_on_open E U s)) ⟨0⟩
    change (E.over U).freeHomEquiv φ ⟨0⟩ = section_on_open E U s at hsec
    rw [← Abelian.image.fac φ, SheafOfModules.freeHomEquiv_comp_apply] at hsec
    have hev := congrArg (fun z ↦ z.val (op (Over.mk (𝟙 U)))) hsec
    change (Abelian.image.ι φ).val.app (op (Over.mk (𝟙 U)))
      (τ.val (op (Over.mk (𝟙 U)))) = E.val.map (𝟙 _) s at hev
    simpa using hev
  have he' := congrArg (fun f ↦ f.val.app (op (Over.mk (𝟙 U)))) he
  change h.val.app (op U) =
    e.hom.val.app (op (Over.mk (𝟙 U))) ≫
      (Abelian.image.ι φ).val.app (op (Over.mk (𝟙 U))) at he'
  rw [he']
  change (Abelian.image.ι φ).val.app (op (Over.mk (𝟙 U)))
    ((e.inv ≫ e.hom).val.app (op (Over.mk (𝟙 U)))
      (τ.val (op (Over.mk (𝟙 U))))) = s
  simpa using ht

/-- A zero-image germ is killed by quotienting by a finite-type quasi-coherent submodule
of the sectionwise kernel. The quotient is finitely presented and the original map factors
through its canonical quotient map.

Source: Stacks Project, Properties, Lemma 01PJ, injectivity paragraph
(blueprint: lem-weil-pbc-finite-presentation-kernel-germ-effacement).

Proof:
1. Represent `s` by a section near `x`. Since its image germ is zero, shrink so its image
   section vanishes. Choose an affine neighbourhood inside the shrinking using the
   affine-open basis;
   affine opens are quasi-compact (def-weil-pbc-module-stalk).
2. Finite presentation makes `G` quasi-coherent. The kernel of `α` is quasi-coherent
   because both `G` and `F` are quasi-coherent, and its sections are the sectionwise kernels.
   The representative of `s` is therefore a section of this kernel on the chosen open
   (def-weil-pbc-module-finite-type-presentation,
   lem-weil-pbc-quasi-coherent-module-kernel).
3. Inside the restricted kernel, take the image of the map from the structure sheaf
   sending `1` to this section. Restriction preserves quasi-coherence, and the image is
   quasi-coherent by transporting the kernel-of-cokernel construction through the
   equivalence with modules on the open subscheme. The finite free generating section
   maps to a generating section of the image, proving finite type directly
   (lem-weil-pbc-module-restriction-open-immersion-colimits,
   def-weil-pbc-module-finite-type-presentation,
   lem-weil-pbc-quasi-coherent-module-cokernel-closure,
   lem-weil-pbc-quasi-coherent-module-kernel).
4. Extend this finite-type quasi-coherent submodule from the quasi-compact open to a
   finite-type quasi-coherent submodule of the kernel on `X` (Stacks 01PF). Compose its
   inclusion with the kernel inclusion to obtain `ι`; every section of it is killed by `α`
   (lem-weil-pbc-module-finite-type-submodule-extension).
5. The cokernel of `ι` is finitely presented, since its source is finite type and its target
   is finitely presented. The cokernel universal property factors `α` through `cokernel.π ι`.
   The representative section belongs to the extended submodule, so its quotient section
   is zero. Taking germs gives the claimed vanishing of the image of `s`
   (lem-weil-pbc-module-finite-presentation-cokernel, def-weil-pbc-module-stalk). -/
theorem exists_finitePresentation_quotient_killing_kernel_germ
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (G F : X.Modules) [SheafOfModules.IsFinitePresentation.{u} G]
    [SheafOfModules.IsQuasicoherent.{u} F] (α : G ⟶ F)
    (x : X) (s : (PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj x).obj G.val)
    (hs : (PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj x).map α.val s = 0) :
    ∃ (K : X.Modules) (ι : K ⟶ G),
      Mono ι ∧ SheafOfModules.IsQuasicoherent.{u} K ∧ SheafOfModules.IsFiniteType.{u} K ∧
        (∀ (U : X.Opens) (t : Γ(K, U)), α.app U (ι.app U t) = 0) ∧
        SheafOfModules.IsFinitePresentation.{u} (cokernel ι) ∧
        (PresheafOfModules.moduleStalkFunctor X.ringCatSheaf.obj x).map
          (cokernel.π ι).val s = 0 ∧
        ∃ β : cokernel ι ⟶ F, cokernel.π ι ≫ β = α := by
  classical
  obtain ⟨V, hxV, t, ht⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf s
  have hzero : TopCat.Presheaf.germ F.val.presheaf V x hxV (α.app V t) = 0 := by
    have h := hs
    rw [← ht] at h
    change PresheafOfModules.stalkAddMap α.val _ = 0 at h
    dsimp only [PresheafOfModules.stalkAddMap] at h
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
    exact h
  obtain ⟨W, hxW, iV, _, heq⟩ := TopCat.Presheaf.germ_eq F.val.presheaf x hxV hxV
    (α.app V t) 0 (by simpa using hzero)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  let i : U ⟶ V := homOfLE (hUW.trans iV.le)
  let tU : Γ(G, U) := G.presheaf.map i.op t
  have htU : α.app U tU = 0 := by
    change α.app U (G.presheaf.map i.op t) = 0
    rw [Hom.app_presheaf_map]
    have he := congrArg (fun z ↦ F.presheaf.map (homOfLE hUW).op z) heq
    change F.val.presheaf.map i.op (α.app V t) = 0
    change F.val.presheaf.map (homOfLE hUW).op
      (F.val.presheaf.map iV.op (α.app V t)) =
      F.val.presheaf.map (homOfLE hUW).op (F.val.presheaf.map _ 0) at he
    have hi : iV.op ≫ (homOfLE hUW).op = i.op := Subsingleton.elim _ _
    simpa only [map_zero, ← Functor.map_comp_apply, hi] using he
  have hsU : TopCat.Presheaf.germ G.val.presheaf U x hxU tU = s :=
    (TopCat.Presheaf.germ_res_apply G.val.presheaf i x hxU t).trans ht
  have : SheafOfModules.IsQuasicoherent.{u} (kernel α) := isQuasicoherent_kernel α
  obtain ⟨k, hk⟩ := (Set.ext_iff.mp (range_map_kernelι U α) tU).mpr htU
  obtain ⟨K, j, l, hKqc, hKft, hj, hl⟩ :=
    finiteType_section_carrier X (kernel α) U hU.isCompact k
  have : Mono j := hj
  have : K.IsFiniteType := hKft
  let ι := j ≫ kernel.ι α
  have hiα : ι ≫ α = 0 := by simp [ι]
  refine ⟨K, ι, inferInstance, hKqc, hKft, ?_,
    RingedSpace.isFinitePresentation_cokernel_of_isFiniteType X.toRingedSpace ι, ?_,
    cokernel.desc ι α hiα, cokernel.π_desc ι α hiα⟩
  · intro T a
    have h := congrArg (fun f ↦ f.app T a) hiα
    simpa [Hom.comp_app] using h
  · have hι : ι.app U l = tU := by
      change (kernel.ι α).app U (j.app U l) = tU
      change (kernel.ι α).val.app (op U) (j.val.app (op U) l) = tU
      rw [hl]
      exact hk
    have hq : (cokernel.π ι).app U tU = 0 := by
      rw [← hι]
      have h := congrArg (fun f ↦ f.app U l) (cokernel.condition ι)
      exact (show (cokernel.π ι).app U (ι.app U l) = 0 from h)
    change PresheafOfModules.stalkAddMap (cokernel.π ι).val s = 0
    rw [← hsU]
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf _).map (cokernel.π ι).val)
        (TopCat.Presheaf.germ G.val.presheaf U x hxU tU) = 0
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change TopCat.Presheaf.germ (cokernel ι).val.presheaf U x hxU ((cokernel.π ι).app U tU) = 0
    rw [hq, map_zero]

end AlgebraicGeometry.Scheme.Modules
