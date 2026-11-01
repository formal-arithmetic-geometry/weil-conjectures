/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCoefficientMap
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleCoherentTotalTensorPullbackComparison
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleTotalTensorPullbackGenerators
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Native ordinary tensor comparison on homogeneous generators

Source: Stacks Tags 03EL and 07A4; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-cochain-tensor)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso proEtaleOrdinaryTensorPullback
  CategoryTheory.Functor.mapBifunctorHomologicalComplex HomologicalComplex₂.total
attribute [local implicit_reducible] coefficientTotalTensor
  CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

private theorem generator_map (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {P P' Q Q' : CochainComplex (pbcModules X R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q')
    (i j : ℤ) (V : X.ProEtᵒᵖ) (x : (P.X i).val.obj V) (y : (Q.X j).val.obj V) :
    (((coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) R).map
      (Prod.mkHom f g)).f (i + j)).val.app V
        (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) R
          P Q i j (i + j) rfl V x y) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) R
        P' Q' i j (i + j) rfl V ((f.f i).val.app V x) ((g.f j).val.app V y) := by
  exact CategoryTheory.ScalarHomTensor.tensor_generator_map
    f g i j (i + j) rfl V x y

set_option maxHeartbeats 3200000 in
-- Transporting total tensor generators checks large universe-polymorphic sheaf instances.
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction in
/-- The native ordinary pullback has a total tensor comparison with precisely the
specified adjunction-unit generator equation. Source: Stacks 03EL, 07A4 and 06YN.
(blueprint: lem-sf-native-pullback-cochain-tensor).

Proof: its right adjoint is the ordinary ringed direct image on the same sections.
Uniqueness of left adjoints therefore identifies native pullback with ordinary
ringed pullback. Transport the signed total tensor comparison along this identification.
The unit equation for uniqueness of adjoints transfers each canonical unit section;
the generator equation for ringed pullback and naturality of the sheafified tensor
then give the displayed equation. Total degrees and signs are unchanged. -/
theorem nativePullbackCochainTensor (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (O : Operations l p R S) (A : At l X R) (C : At l Y S) :
    ∃ e : coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S) ⋙
        (ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ) ≅
      (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).prod
        ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ))) ⋙
          coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R),
      tensorPure l p R S O A C e := by
  letI hO : IsIso O.coefficient := nativePullbackCoefficient_isIso l p R S O
  let c := asIso O.coefficient
  let G := proEtaleRingModulePullback p (ring l Y S) (ring l X R) c
  let H := ContinuousRational.modulePull p O.coefficient
  let r : proEtaleRingModuleDirectImage p (ring l Y S) (ring l X R) c ≅
      ContinuousRational.DirectImage.modulePush p O.coefficient := Iso.refl _
  let a := (proEtaleRingModuleAdjunction p (ring l Y S) (ring l X R) c).ofNatIsoRight r
  let q : G ≅ H := a.leftAdjointUniq O.moduleAdjunction
  have hu (M : modules l Y S) (V : Y.ProEt) (m : M.val.obj (op V)) :
      (q.hom.app M).val.app (op ((proEtaleBaseChange p).obj V))
        (((proEtaleRingModuleAdjunction p (ring l Y S) (ring l X R) c).unit.app M).val.app
          (op V) m) = (O.moduleAdjunction.unit.app M).val.app (op V) m := by
    exact congrArg (fun z ↦ z.val.app (op V) m)
      (a.unit_leftAdjointUniq_hom_app O.moduleAdjunction M)
  let qC := NatIso.mapHomologicalComplex q (.up ℤ)
  let tX := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  let tY := coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S)
  obtain ⟨b, hb, _⟩ := proEtaleCoherentTotalTensorPullbackComparison p
    (ring l Y S) (ring l X R) c
  let b' : ((G.mapHomologicalComplex (.up ℤ)).prod
      (G.mapHomologicalComplex (.up ℤ))) ⋙ tX ≅ tY ⋙ G.mapHomologicalComplex (.up ℤ) := by
    exact b
  let e : tY ⋙ H.mapHomologicalComplex (.up ℤ) ≅
      ((H.mapHomologicalComplex (.up ℤ)).prod
        (H.mapHomologicalComplex (.up ℤ))) ⋙ tX :=
    Functor.isoWhiskerLeft tY qC.symm ≪≫ b'.symm ≪≫
    Functor.isoWhiskerRight (NatIso.prod qC qC) tX
  refine ⟨e, ?_⟩
  intro P Q i j V x y
  let U := op ((proEtaleBaseChange p).obj V)
  have hunit (M : modules l Y S) (m : M.val.obj (op V)) :
      (q.inv.app M).val.app U ((O.moduleAdjunction.unit.app M).val.app (op V) m) =
        (((proEtaleRingModuleAdjunction p (ring l Y S) (ring l X R) c).unit.app M).val.app
          (op V) m) := by
    rw [← hu M V m]
    exact congrArg (fun z ↦ z.val.app U
      (((proEtaleRingModuleAdjunction p (ring l Y S) (ring l X R) c).unit.app M).val.app
        (op V) m)) (q.hom_inv_id_app M)
  change ((tX.map (Prod.mkHom (qC.hom.app P) (qC.hom.app Q))).f (i + j)).val.app U
    (((b'.inv.app (P, Q)).f (i + j)).val.app U
      ((q.inv.app _).val.app U _)) = _
  let τ := fun z ↦
    ((tX.map (Prod.mkHom (qC.hom.app P) (qC.hom.app Q))).f (i + j)).val.app U z
  let β := fun z ↦ ((b'.inv.app (P, Q)).f (i + j)).val.app U z
  let z := coefficientTensorGenerator.{u + 1, u + 1, u}
    (ProEt.topology Y) (ring l Y S) P Q i j (i + j) rfl (op V) x y
  let η := (proEtaleRingModuleAdjunction p (ring l Y S) (ring l X R) c).unit
  have h0 := congrArg (fun w ↦ τ (β w)) (hunit ((tY.obj (P, Q)).X (i + j)) z)
  have h1 := congrArg (fun f ↦ τ ((f.f (i + j)).val.app U
    ((η.app ((tY.obj (P, Q)).X (i + j))).val.app (op V) z))) (hb P Q)
  have h2 := congrArg τ (proEtaleTensorPullbackTotal_generators p
    (ring l Y S) (ring l X R) c P Q i j (i + j) rfl V x y)
  have h3 := generator_map X (ring l X R) (qC.hom.app P) (qC.hom.app Q) i j U
    ((η.app (P.X i)).val.app (op V) x) ((η.app (Q.X j)).val.app (op V) y)
  have h4 := congrArg₂ (fun w z ↦ coefficientTensorGenerator.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R)
      ((H.mapHomologicalComplex (.up ℤ)).obj P)
      ((H.mapHomologicalComplex (.up ℤ)).obj Q) i j (i + j) rfl U w z)
    (hu (P.X i) V x) (hu (Q.X j) V y)
  exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

end WeilConjectures.AdicQbarRealization.Proper
