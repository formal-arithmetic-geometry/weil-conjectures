/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # The ordinary terminal-sections unit

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2).
(blueprint: lem-zl-contractible-realization-ordinary-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

private theorem module_natTrans_isIso
    {R : Type (u + 1)} [CommRing R]
    {F G : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R}
    [PreservesColimitsOfSize.{u + 1, u + 1} F]
    [PreservesColimitsOfSize.{u + 1, u + 1} G]
    (τ : F ⟶ G) (h : IsIso (τ.app (ModuleCat.of R R))) : IsIso τ := by
  classical
  have free_iso (I : Type (u + 1)) : IsIso (τ.app ((ModuleCat.free R).obj I)) := by
    let K := Discrete.functor (fun _ : I ↦ ModuleCat.of R R)
    have : IsIso (Functor.whiskerLeft K τ) := by
      have (i : Discrete I) : IsIso ((Functor.whiskerLeft K τ).app i) := h
      exact NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit K τ
      (ModuleCat.finsuppCocone R R I) (ModuleCat.finsuppCoconeIsColimit R R I)
  have all_iso (M : ModuleCat.{u + 1} R) : IsIso (τ.app M) := by
    let Q := (ModuleCat.free R).obj M
    let g : Q ⟶ M := ModuleCat.freeDesc (↾fun x ↦ x)
    let P := (ModuleCat.free R).obj g.hom.ker
    let f : P ⟶ Q := ModuleCat.freeDesc (↾fun x : g.hom.ker ↦ x.val)
    have w : f ≫ g = 0 := by
      apply ModuleCat.free_hom_ext
      intro x
      simp [f, g]
    have he : Function.Exact f.hom g.hom := by
      intro x
      constructor
      · intro hx
        exact ⟨ModuleCat.freeMk (R := R) (⟨x, hx⟩ : g.hom.ker),
          ModuleCat.freeDesc_apply _ _⟩
      · rintro ⟨y, rfl⟩
        exact congrArg (fun k : P ⟶ M ↦ k y) w
    have hg : Function.Surjective g.hom := fun x ↦
      ⟨ModuleCat.freeMk x, ModuleCat.freeDesc_apply _ _⟩
    let K := parallelPair f 0
    have : IsIso (Functor.whiskerLeft K τ) := by
      have (j : WalkingParallelPair) : IsIso ((Functor.whiskerLeft K τ).app j) := by
        cases j
        · exact free_iso g.hom.ker
        · exact free_iso M
      exact NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit K τ
      (CokernelCofork.ofπ g w) (ModuleCat.isColimitCokernelCofork f g he hg)
  exact NatIso.isIso_of_isIso_app τ

private def terminalSectionsEquiv
    {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    (U : C) (hU : IsTerminal U) (M : SheafOfModules.{u + 1} R) :
    M.sections ≃ M.val.obj (op U) where
  toFun s := s.val (op U)
  invFun x := M.val.sectionsMk (fun V ↦ M.val.map (hU.from V.unop).op x) (by
    intro V W f
    rw [← PresheafOfModules.map_comp_apply]
    have hh : f.unop ≫ hU.from V.unop = hU.from W.unop := hU.hom_ext _ _
    exact M.val.congr_map_apply (by
      apply Quiver.Hom.unop_inj
      exact hh) x)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    exact s.property (hU.from V.unop).op
  right_inv x := by
    change M.val.map (hU.from U).op x = x
    have hh : hU.from U = 𝟙 U := hU.hom_ext _ _
    rw [hh]
    simp

/-- The ordinary realization/sections unit is invertible when terminal sections are
preserve small colimits.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2).
(blueprint: lem-zl-contractible-realization-ordinary-unit).

Proof: any left adjoint to sections is uniquely isomorphic, as an adjunction, to
sheafification of V ↦ O(V) tensor_A M. At M=A its unit identifies with the identity
of O(U)=A, since U is terminal. The left adjoint and sections (by hcol) preserve coproducts,
so the unit is invertible for free modules of arbitrary allowed rank. Every A-module
admits a presentation by two free modules. Realization preserves its cokernel as a
left adjoint, and sections preserve the cokernel by hcol. The natural
map between these two cokernel presentations is an isomorphism on the free terms,
hence on their cokernels. This is precisely the unit on M. -/
theorem contractible_realization_ordinary_unit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U)
    (hcol : PreservesColimitsOfSize.{u + 1, u + 1} (sections J O U)) :
    ∀ (L : ModuleCat.{u + 1} (A J O U) ⥤ Mod (Sheaf J Ab.{u + 1}) O)
      (adj : L ⊣ sections J O U), IsIso adj.unit := by
  intro L adj
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (ringSheaf J O)
  let B := e.inverse.obj (SheafOfModules.unit R)
  let T := sections J O U ⋙ forget (ModuleCat.{u + 1} (A J O U))
  let p : T.CorepresentableBy (L.obj (ModuleCat.of (A J O U) (A J O U))) :=
    { homEquiv := fun {M} ↦ (adj.homEquiv _ M).trans
        (ModuleCat.homEquiv.trans
          (LinearMap.ringLmapEquivSelf (A J O U) ℤ ((sections J O U).obj M)).toEquiv)
      homEquiv_comp := by
        intro M N f g
        simp only [Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
        rfl }
  let q : T.CorepresentableBy B :=
    { homEquiv := fun {M} ↦ (e.symm.toAdjunction.homEquiv (SheafOfModules.unit R) M).trans
        ((SheafOfModules.unitHomEquiv (e.functor.obj M)).trans
          (terminalSectionsEquiv U hU (e.functor.obj M)))
      homEquiv_comp := by
        intro M N f g
        simp only [Equiv.trans_apply]
        rfl }
  let i : L.obj (ModuleCat.of (A J O U) (A J O U)) ≅ B := p.uniqueUpToIso q
  let j : ModuleCat.of (A J O U) (A J O U) ≅ (sections J O U).obj B :=
    (SheafOfModules.evaluation R (op U)).mapIso
      (e.counitIso.app (SheafOfModules.unit R)).symm
  have hi : adj.unit.app (ModuleCat.of (A J O U) (A J O U)) ≫
      (sections J O U).map i.hom = j.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change p.homEquiv i.hom = j.hom 1
    change p.homEquiv (p.homEquiv.symm (q.homEquiv (𝟙 B))) = j.hom 1
    rw [Equiv.apply_symm_apply]
    simp only [q, Equiv.trans_apply]
    rfl
  have hunit : IsIso (adj.unit.app (ModuleCat.of (A J O U) (A J O U))) := by
    have : IsIso (adj.unit.app (ModuleCat.of (A J O U) (A J O U)) ≫
        (sections J O U).map i.hom) := by rw [hi]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((sections J O U).map i.hom)
  have : PreservesColimitsOfSize.{u + 1, u + 1} L := adj.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u + 1, u + 1} (sections J O U) := hcol
  exact module_natTrans_isIso adj.unit hunit

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
