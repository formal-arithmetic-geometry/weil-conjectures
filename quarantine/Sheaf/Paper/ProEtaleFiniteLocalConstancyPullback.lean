/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Finite local constancy under inverse image

Source: Stacks Project, Modules on Sites, Tag 093R;
Etale Cohomology, Tag 095I (common stratifications).
(blueprint: lem-pur-proetale-finite-local-constancy-pullback).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The coefficient direct-image map extends the constant-section unit.
Source: Stacks Project, Tag 0H7J, the constant-sheaf universal property.
(blueprint: lem-pur-proetale-finite-local-constancy-pullback). -/
theorem proEtaleConstantModulePullback_rho_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u)
    [CommRing A] (W : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app W ≫
      (proEtaleCoefficientDirectImageMap f A).hom.app W =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app
        ((proEtaleBaseChange f).op.obj W) := by
  have h := (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A))
    |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))))
  exact congrArg (fun t ↦ t.app W) h

/-- The ring direct-image map is the adjunct of the canonical coefficient comparison.
Source: Stacks Project, Tag 03D2, inverse-image/direct-image adjunction.
(blueprint: lem-pur-proetale-finite-local-constancy-pullback). -/
theorem proEtaleConstantModulePullback_ring_direct
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    [IsIso (proEtaleCoefficientInverseImageMap f A)] :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (asIso (proEtaleCoefficientInverseImageMap f A)) =
        proEtaleCoefficientDirectImageMap f A := by
  exact (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    |>.apply_symm_apply (proEtaleCoefficientDirectImageMap f A)

/-- Inverse image preserves finite local constancy of a module sheaf.

Source: Stacks Project, Modules on Sites, Tag 093R,
lemma-pullback-locally-constant, applied to pro-etale module inverse image.
(blueprint: lem-pur-proetale-finite-local-constancy-pullback).

Proof: use the coefficient-encoding equivalence to express F by finite constant
models on a pro-etale cover. Pull this cover back along b; precoverage stability
under base change preserves its covering property. The pullback composition
isomorphisms and the cartesian-square equation identify each new restriction with
the pullback of its old constant model. A terminal-object-preserving site inverse
image commutes with constant sheaves, so each new model has the same finite value.
Finally restriction to constant scalars commutes with the specified intrinsic
module pullback. Transport the finite-model condition through this comparison and
back through the coefficient-encoding equivalence. That equivalence supplies both
local constancy on localized ringed sites and finiteness of every geometric stalk.
The argument also covers empty schemes, empty covering members and the zero ring. -/
theorem proEtale_finiteLocalConstancy_pullback
    {Y X : Scheme.{u}} (b : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (hF : IsLocallyConstantProEtaleModuleSheaf Y A F ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)) :
    IsLocallyConstantProEtaleModuleSheaf X A (proEtaleConstantModulePullback b A F) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A)
          (proEtaleConstantModulePullback b A F)) := by
  let Λ := ULift.{u + 1, u} A
  let G := (proEtaleModuleRestriction Y A).obj F
  have hG : ProEtale.IsFiniteLocallyConstant Λ G := (finiteLocal_iff Y A F).mpr hF
  obtain ⟨I, W, g, hg, hm⟩ := hG
  have hp : ProEtale.IsFiniteLocallyConstant Λ
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) b).obj G) := by
    refine ⟨I, fun i ↦ pullback (g i) b, fun i ↦ pullback.snd (g i) b, ?_, ?_⟩
    · exact Precoverage.mem_coverings_of_isPullback g hg b _ _
        (fun i ↦ (IsPullback.of_hasPullback (g i) b).flip)
    · intro i
      obtain ⟨M, hM, ⟨e⟩⟩ := hm i
      let p := pullback.fst (g i) b
      let q := pullback.snd (g i) b
      let E := ModuleCat.{u + 1} Λ
      have heq : q ≫ b = p ≫ g i := pullback.condition.symm
      exact ⟨M, hM, ⟨
        ((ProEtale.upperStarComp E q b).app G).symm ≪≫
        (eqToIso (congrArg (fun f ↦ (ProEtale.upperStar E f).obj G) heq)) ≪≫
        (ProEtale.upperStarComp E p (g i)).app G ≪≫
        (ProEtale.upperStar E p).mapIso e ≪≫
        (Functor.isoWhiskerLeft (constantSheaf (ProEt.topology (W i)) E)
          (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange p) E
            (ProEt.topology (W i)) (ProEt.topology (pullback (g i) b))).symm).app M ≪≫
        ((proEtaleBaseChange p).constantSheafsheafPullbackIso E
          (ProEt.topology (W i)) (ProEt.topology (pullback (g i) b))
          (ProEt.isTerminalMkId (W i))
          ((ProEt.isTerminalMkId (W i)).isTerminalObj (proEtaleBaseChange p) _)).app M⟩⟩
  obtain ⟨e⟩ := proEtaleModuleRestriction_pullback b A F
  exact (finiteLocal_iff X A _).mp
    (ProEtale.isFiniteLocallyConstant_of_iso e.symm hp)

end AlgebraicGeometry.Scheme
