/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.AffineTensorPullbackHomologyComparison
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! # Square-zero tests detect tensor exactness on an affine scheme

Source: the square-zero test in the proof of
lem-pc-affine-universally-exact-opcycles-flat, using Stacks Project, Tag 01IB.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Scheme base-change tests imply module tensor exactness in a fixed degree.
Source: Stacks Project, Tag 01IB, and steps 1--2 of
lem-pc-affine-universally-exact-opcycles-flat. -/
theorem affine_universal_tensor_exact (S : Scheme.{u}) (hS : IsAffine S)
    (C : CochainComplex S.Modules ℤ) (a : ℤ)
    (hqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hexact : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology a))
    (N : ModuleCat.{u} Γ(S, ⊤)) :
    (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj
      (((SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤) :
        S.Modules ⥤ ModuleCat.{u} Γ(S, ⊤)).mapHomologicalComplex
        (.up ℤ)).obj C)).ExactAt a := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
      let A := Γ(S, ⊤)
      let : Module Aᵐᵒᵖ N :=
        Module.compHom N ((RingHom.id A).fromOpposite (fun _ _ ↦ mul_comm _ _))
      have : IsCentralScalar A N := ⟨fun _ _ ↦ rfl⟩
      let B : Type u := TrivSqZeroExt A N
      let P : CochainComplex (ModuleCat.{u} A) ℤ :=
        ((SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤) :
          S.Modules ⥤ ModuleCat.{u} A).mapHomologicalComplex (.up ℤ)).obj C
      let j : N ⟶ ModuleCat.of A B := ModuleCat.ofHom (TrivSqZeroExt.inrHom A N)
      let p : ModuleCat.of A B ⟶ N := ModuleCat.ofHom (TrivSqZeroExt.sndHom A N)
      have hjp : j ≫ p = 𝟙 N := by
        ext x
        rfl
      let i := ((tensoringRight (ModuleCat.{u} A)).map j).mapHomologicalComplex (.up ℤ)
      let r := ((tensoringRight (ModuleCat.{u} A)).map p).mapHomologicalComplex (.up ℤ)
      have hir : i.app P ≫ r.app P = 𝟙 _ := by
        rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
          ← Functor.map_comp, hjp]
        rw [(tensoringRight (ModuleCat.{u} A)).map_id N,
          NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
      have hS' : IsAffine S := hS
      obtain ⟨e⟩ := affine_tensor_pullback_homology_comparison S C hqc B a
      let E := moduleSpecΓFunctor (R := CommRingCat.of B)
      let : E.IsRightAdjoint := (tilde.adjunction (R := CommRingCat.of B)).isRightAdjoint
      let := preservesBinaryBiproducts_of_preservesBinaryProducts E
      let : E.Additive := Functor.additive_of_preservesBinaryBiproducts E
      have hz : IsZero (E.obj _) := Functor.map_isZero
        (moduleSpecΓFunctor (R := CommRingCat.of B))
        (hexact (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ S.isoSpec.inv))
      have hz' := (Functor.map_isZero (ModuleCat.restrictScalars (algebraMap A B)) hz).of_iso e
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) a
      apply (IsZero.iff_id_eq_zero _).2
      have h := congrArg H.map hir
      rw [H.map_comp, H.map_id] at h
      exact h.symm.trans (by
        rw [hz'.eq_of_tgt (H.map (i.app P)) 0, zero_comp])


end AlgebraicGeometry.Scheme.Modules
