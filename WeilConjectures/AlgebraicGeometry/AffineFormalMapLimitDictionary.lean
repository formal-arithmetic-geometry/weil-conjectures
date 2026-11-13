/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineGlobalComparison
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-! # Affine formal maps and inverse limits of sections

Source: Stacks Project, Tags 087W, 00MA and 0889(1).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A coherent affine tilde presentation has a finite module of coefficients
(Stacks, Tags 01IB, 01PB and 01XZ). -/
private theorem finite_presentation_module
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X]
    (H : CoherentModules X) (P : ModuleCat.{u} Γ(X, ⊤))
    (ε : (tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.pullback X.isoSpec.hom).obj P ≅ H.obj) :
    Module.Finite Γ(X, ⊤) P := by
  have hH := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X H.obj).mp H.property
  have : H.obj.IsQuasicoherent := hH.1
  have : H.obj.IsFiniteType := hH.2
  have : Module.Finite Γ(X, ⊤) Γ(H.obj, ⊤) :=
    (Scheme.Modules.affine_finiteType_generatingSections X H.obj).1
  let M := H.obj.restrict X.isoSpec.inv
  let e₀ := Scheme.Modules.sectionsRestrictFromSpecLinearEquiv H.obj (isAffineOpen_top X)
  have : Module.Finite Γ(X, ⊤) (moduleSpecΓFunctor.obj M) := by
    apply Module.Finite.equiv
      (show Γ(H.obj, ⊤) ≃ₗ[Γ(X, ⊤)] (moduleSpecΓFunctor.obj M) from ?_)
    exact e₀.symm ≪≫ₗ (moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.restrictFunctorCongr (IsAffineOpen.fromSpec_top (X := X))).app
        H.obj)).toLinearEquiv
  let T := tilde.functor Γ(X, ⊤)
  let R := Scheme.Modules.restrictFunctor X.isoSpec.inv
  let e : T.obj P ≅ M :=
    ((Scheme.Modules.restrictFunctorId (X := Spec Γ(X, ⊤))).app (T.obj P)).symm ≪≫
    ((Scheme.Modules.restrictFunctorCongr X.isoSpec.inv_hom_id).app (T.obj P)).symm ≪≫
    (Scheme.Modules.restrictFunctorComp X.isoSpec.inv X.isoSpec.hom).app (T.obj P) ≪≫
    R.mapIso ((Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.hom).app (T.obj P)) ≪≫
    R.mapIso ε
  let eP := (tilde.toTildeΓNatIso (R := Γ(X, ⊤))).app P ≪≫
    moduleSpecΓFunctor.mapIso e
  exact Module.Finite.equiv eP.toLinearEquiv.symm

set_option maxHeartbeats 1000000 in
-- The affine equivalence and two natural comparisons require extra elaboration heartbeats.
/-- The affine dictionary identifies a formal morphism with a completed linear map,
and identifies that map with the actual inverse limit of its section maps.
No torsion hypothesis or annihilator conclusion is involved
(Stacks, Tags 087W, 00MA, 0889 and 0888). -/
theorem affine_formal_map_limit_dictionary
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let S := AdicCompletion I A
    let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
    let C := L ⋙ formalCompletionFunctor J
    ∀ (P : ModuleCat.{u} A) (ε : L.obj P ≅ H.obj)
      (η : C.obj P ≅ C.obj (ModuleCat.of A (S ⊗[A] P))),
    ∃ Q : ModuleCat.{u} S,
      letI := Module.restrictScalars A S Q
      letI := IsScalarTower.restrictScalars A S Q
      ∃ (φ : Q →ₗ[S] S ⊗[A] P)
        (ρ : N.obj ≅ C.obj (ModuleCat.of A Q))
        (a : Q ≃ₗ[A] ↥(limit (N.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) : ModuleCat A))
        (b : (S ⊗[A] P) ≃ₗ[A] ↥(limit (((completion X J).obj H).obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) : ModuleCat A)),
        δ.hom = ρ.hom ≫ C.map (ModuleCat.ofHom (φ.restrictScalars A)) ≫
          η.inv ≫ (formalCompletionFunctor J).map ε.hom ∧
        ∀ x : Q, b (φ x) =
          (lim.map (Functor.whiskerRight δ.hom
            (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))).hom (a x) := by
  classical
  dsimp only
  intro P ε η
  let A := Γ(X, ⊤)
  let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
  let S := AdicCompletion I A
  let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
  let C := L ⋙ formalCompletionFunctor J
  let R := ObjectProperty.ι (fun Q : ModuleCat.{u} S ↦ Module.Finite S Q) ⋙
    ModuleCat.restrictScalars (algebraMap A S)
  let ι := (IsCoherentFormalModule J).ι
  let W := (Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat A)).obj
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
  let D := W ⋙ lim
  have : Module.Finite A P := finite_presentation_module H P ε
  have : Module.Finite S (S ⊗[A] P) := inferInstance
  obtain ⟨E, ⟨β⟩, ⟨γ⟩⟩ := coherentFormalModules_affine_global_comparison X J
  let Q := E.inverse.obj N
  let := Module.restrictScalars A S Q.obj
  let := IsScalarTower.restrictScalars A S Q.obj
  let B : ObjectProperty.FullSubcategory
      (fun Q : ModuleCat.{u} S ↦ Module.Finite S Q) :=
    ⟨ModuleCat.of S (S ⊗[A] P), inferInstance⟩
  let c := E.counitIso.app N
  let t : (E.functor.obj B).obj ≅ ((completion X J).obj H).obj :=
    β.app B ≪≫ η.symm ≪≫ (formalCompletionFunctor J).mapIso ε
  let t' : E.functor.obj B ≅ (completion X J).obj H := ι.preimageIso t
  let f : E.functor.obj Q ⟶ E.functor.obj B := c.hom ≫ δ ≫ t'.inv
  let ψ : Q ⟶ B := E.functor.preimage f
  have hψ : E.functor.map ψ = f := E.functor.map_preimage f
  have hψt : ι.map (E.functor.map ψ) ≫ t.hom = ι.map c.hom ≫ δ.hom := by
    rw [hψ]
    change (ι.map c.hom ≫ δ.hom ≫ ι.map t'.inv) ≫ t.hom = _
    have ht : ι.map t'.inv = t.inv := by simp [t', Functor.preimageIso]
    rw [ht]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let ρ : N.obj ≅ C.obj (ModuleCat.of A Q.obj) :=
    ι.mapIso c.symm ≪≫ β.app Q
  let a : Q.obj ≃ₗ[A] ↥(limit (N.obj ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) : ModuleCat A) :=
    (γ.app Q ≪≫ D.mapIso (ι.mapIso c)).toLinearEquiv
  let b : (S ⊗[A] P) ≃ₗ[A] ↥(limit (((completion X J).obj H).obj ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) : ModuleCat A) :=
    (γ.app B ≪≫ D.mapIso t).toLinearEquiv
  refine ⟨Q.obj, ψ.hom.hom, ρ, a, b, ?_, ?_⟩
  · symm
    have hβ := β.hom.naturality ψ
    change ι.map (E.functor.map ψ) ≫ (β.app B).hom =
      (β.app Q).hom ≫ C.map (R.map ψ) at hβ
    change (ι.map c.inv ≫ (β.app Q).hom) ≫ C.map (R.map ψ) ≫
      η.inv ≫ (formalCompletionFunctor J).map ε.hom = δ.hom
    rw [Category.assoc, ← Category.assoc (β.app Q).hom (C.map (R.map ψ)), ← hβ]
    change ι.map c.inv ≫ ι.map (E.functor.map ψ) ≫ t.hom = δ.hom
    rw [hψt, ← ι.map_comp_assoc, c.inv_hom_id]
    simp
  · have hγ := γ.hom.naturality ψ
    change R.map ψ ≫ (γ.app B).hom =
      (γ.app Q).hom ≫ D.map (ι.map (E.functor.map ψ)) at hγ
    have hs : R.map ψ ≫ ((γ.app B).hom ≫ D.map t.hom) =
        ((γ.app Q).hom ≫ D.map (ι.map c.hom)) ≫ D.map δ.hom := by
      rw [← Category.assoc, hγ, Category.assoc, ← D.map_comp, hψt,
        D.map_comp, Category.assoc]
    intro x
    exact congrArg (fun g ↦ g x) hs

end AlgebraicGeometry
