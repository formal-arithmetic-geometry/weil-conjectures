/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitRightRepresentatives
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackUnitComplex
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackExactCounits
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCoefficientMap
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitLeftRepresentatives
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorCoherence

/-! # The normalized derived left-unit equation for arbitrary native pullback

Source: Bhatt--Scholze Remark 6.8.15; Stacks Tags 03EK and 0FPT.
(blueprint: lem-sf-native-pullback-left-unitor)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard WeilConjectures.coefficientTotalTensor
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite WeilConjectures CategoryTheory.RingedForgetTensorTransposition
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  {R : LocallyFiniteAdicRealization.Realization l X}
  {S : LocallyFiniteAdicRealization.Realization l Y}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  {O : Operations l p R S} {A : At l X R} {C : At l Y S}
  (V : TensorComparison l p R S O A C)

set_option maxHeartbeats 800000 in
-- The representative calculation transports several large sheaf tensor models.
/-- The normalized native derived tensor comparison preserves the left unitor.
Source: BS Remark 6.8.15; Stacks 03EK and 0FPT.
(blueprint: lem-sf-native-pullback-left-unitor).

Proof: choose a K-flat representative P. The coefficient unit and its pullback are
K-flat. Use the two prescribed tensor-model isomorphisms and their naturality to
transport the cochain left-unit equation to the derived tensor square. Exactness
makes O's normalized cochain counit an isomorphism on all complexes. Its naturality
identifies the cochain and derived pullback routes. The unit representative equation
identifies the resulting unit map with V.unit. Finally transport along Q(P) isomorphic
to the original object. -/
theorem nativePullbackLeftUnitor (M : DerivedCategory (modules l Y S)) :
    V.tensor.hom.app (C.closed.monoidal.tensorUnit, M) ≫
      A.closed.tensor.map (Prod.mkHom V.unit.hom (𝟙 _)) ≫
      (A.closed.monoidal.leftUnitor ((ContinuousRational.derivedPull p O.coefficient).obj M)).hom =
    (ContinuousRational.derivedPull p O.coefficient).map (C.closed.monoidal.leftUnitor M).hom := by
  have := nativePullbackCoefficient_isIso l p R S O
  obtain ⟨P, hP, _, ⟨eM⟩⟩ :=
    flat_representative.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S) M
  apply left_unit_of_iso C.closed A.closed (ContinuousRational.derivedPull p O.coefficient) V.tensor
    V.unit eM
  let F := (ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)
  let U := ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)
  let U' := ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)
  have hO := unit_kflat.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)
  have hO' := unit_kflat.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)
  have hFP := V.kflat P hP
  have hFO := V.kflat U hO
  obtain ⟨bB, hbB, heB⟩ := C.coherence.leftUnitor_model P hP
  obtain ⟨bA, hbA, heA⟩ := A.coherence.leftUnitor_model (F.obj P) hFP
  rw [C.coherence.tensorIso_both U P hO hP] at heB
  rw [A.coherence.tensorIso_both U' (F.obj P) hO' hFP] at heA
  have hc := nativePullbackLeftUnitorChain l p V P bB bA hbB hbA
  have hδ (P : CochainComplex (modules l Y S) ℤ) : IsIso (O.pullCounit.app P) :=
    nativePullbackNormalizedCounit_isIso p O.coefficient O.pullCounit O.pull_normalized P
  have : IsIso O.pullCounit :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ O.pullCounit hδ
  let α := asIso O.pullCounit
  let t := (coefficientTotalTensor.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R)).mapIso
      (V.unitCochain.prod (Iso.refl (F.obj P)))
  let c := α.app ((coefficientTotalTensor.{u + 1, u + 1, u}
    (ProEt.topology Y) (ring l Y S)).obj (U, P)) ≪≫
    DerivedCategory.Q.mapIso (V.cochain.app (U, P)) ≪≫ DerivedCategory.Q.mapIso t
  have hm : (ContinuousRational.derivedPull p O.coefficient).map
      (C.models.iso _ _ _ U P hO hP).hom ≫
      V.tensor.hom.app (DerivedCategory.Q.obj U, DerivedCategory.Q.obj P) ≫
      A.closed.tensor.map
        (X := ((ContinuousRational.derivedPull p O.coefficient).obj (DerivedCategory.Q.obj U),
          (ContinuousRational.derivedPull p O.coefficient).obj (DerivedCategory.Q.obj P)))
        (Y := (DerivedCategory.Q.obj U', DerivedCategory.Q.obj (F.obj P)))
        ((α.app U ≪≫ DerivedCategory.Q.mapIso V.unitCochain).hom, (α.app P).hom) =
      c.hom ≫ (A.models.iso _ _ _ U' (F.obj P) hO' hFP).hom := by
    have hm := V.representative U P hO hP
    have hn := A.coherence.tensorIso_naturality (F.obj U) (F.obj P) U' (F.obj P)
      (Or.inr hFP) (Or.inr hFP) V.unitCochain.hom (𝟙 _)
    rw [A.coherence.tensorIso_both _ _ hFO hFP,
      A.coherence.tensorIso_both _ _ hO' hFP] at hn
    let := A.closed.monoidal
    calc
      _ = (ContinuousRational.derivedPull p O.coefficient).map (C.models.iso _ _ _ U P hO hP).hom ≫
          V.tensor.hom.app (DerivedCategory.Q.obj U, DerivedCategory.Q.obj P) ≫
          A.closed.tensor.map
            (X := ((ContinuousRational.derivedPull p O.coefficient).obj (DerivedCategory.Q.obj U),
              (ContinuousRational.derivedPull p O.coefficient).obj (DerivedCategory.Q.obj P)))
            (Y := (DerivedCategory.Q.obj (F.obj U), DerivedCategory.Q.obj (F.obj P)))
            ((α.app U).hom, (α.app P).hom) ≫
          A.closed.tensor.map
            (X := (DerivedCategory.Q.obj (F.obj U), DerivedCategory.Q.obj (F.obj P)))
            (Y := (DerivedCategory.Q.obj U', DerivedCategory.Q.obj (F.obj P)))
            (DerivedCategory.Q.map V.unitCochain.hom, 𝟙 _) := by
        simp only [Iso.trans_hom, Functor.mapIso_hom, CoefficientClosedStructure.tensor,
          tensor_map, tensorHom_comp_tensorHom, Category.comp_id]
      _ = (α.app _).hom ≫ DerivedCategory.Q.map (V.cochain.hom.app (U, P)) ≫
          (A.models.iso _ _ _ (F.obj U) (F.obj P) hFO hFP).hom ≫
          A.closed.tensor.map
            (X := (DerivedCategory.Q.obj (F.obj U), DerivedCategory.Q.obj (F.obj P)))
            (Y := (DerivedCategory.Q.obj U', DerivedCategory.Q.obj (F.obj P)))
            (DerivedCategory.Q.map V.unitCochain.hom, 𝟙 _) := by
        simpa only [Category.assoc, α, F, Iso.app_hom, asIso_hom] using
          congrArg (fun f ↦ f ≫ A.closed.tensor.map
            (X := (DerivedCategory.Q.obj (F.obj U), DerivedCategory.Q.obj (F.obj P)))
            (Y := (DerivedCategory.Q.obj U', DerivedCategory.Q.obj (F.obj P)))
            (DerivedCategory.Q.map V.unitCochain.hom, 𝟙 _)) hm
      _ = _ := by
        have hn' : DerivedCategory.Q.map t.hom ≫
            (A.models.iso _ _ _ U' (F.obj P) hO' hFP).hom =
            (A.models.iso _ _ _ (F.obj U) (F.obj P) hFO hFP).hom ≫
              A.closed.tensor.map
                (X := (DerivedCategory.Q.obj (F.obj U), DerivedCategory.Q.obj (F.obj P)))
                (Y := (DerivedCategory.Q.obj U', DerivedCategory.Q.obj (F.obj P)))
                (DerivedCategory.Q.map V.unitCochain.hom, 𝟙 _) := by
          have hn0 : DerivedCategory.Q.map t.hom ≫
              (A.models.iso _ _ _ U' (F.obj P) hO' hFP).hom =
              (A.models.iso _ _ _ (F.obj U) (F.obj P) hFO hFP).hom ≫
                A.closed.tensor.map
                  (X := (DerivedCategory.Q.obj (F.obj U), DerivedCategory.Q.obj (F.obj P)))
                  (Y := (DerivedCategory.Q.obj U', DerivedCategory.Q.obj (F.obj P)))
                  (DerivedCategory.Q.map V.unitCochain.hom,
                    DerivedCategory.Q.map (𝟙 (F.obj P))) := by
            simpa only [t, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
              Prod.mkHom, F, U'] using hn
          exact hn0.trans (congrArg (fun f ↦
            (A.models.iso _ _ _ (F.obj U) (F.obj P) hFO hFP).hom ≫
              A.closed.tensor.map
                (X := (DerivedCategory.Q.obj (F.obj U), DerivedCategory.Q.obj (F.obj P)))
                (Y := (DerivedCategory.Q.obj U', DerivedCategory.Q.obj (F.obj P)))
                (DerivedCategory.Q.map V.unitCochain.hom, f))
            (DerivedCategory.Q.map_id (F.obj P)))
        simpa only [c, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
          Category.assoc] using
          congrArg (fun f ↦ (α.app _).hom ≫
            DerivedCategory.Q.map (V.cochain.hom.app (U, P)) ≫ f) hn'.symm
  have hf : (ContinuousRational.derivedPull p O.coefficient).map (DerivedCategory.Q.map bB.hom) ≫
      (α.app P).hom = c.hom ≫ DerivedCategory.Q.map bA.hom := by
    have hn := α.hom.naturality bB.hom
    change (ContinuousRational.derivedPull p O.coefficient).map
        (DerivedCategory.Q.map bB.hom) ≫ (α.app P).hom =
      (α.app _).hom ≫ DerivedCategory.Q.map (F.map bB.hom) at hn
    rw [hn, hc]
    simp only [Functor.map_comp, c, Iso.trans_hom, Functor.mapIso_hom,
      t, Iso.prod_hom, Iso.refl_hom, Iso.app_hom, Prod.mkHom, Category.assoc, U, F]
  have hh := left_unit_of_models C.closed A.closed
    (ContinuousRational.derivedPull p O.coefficient) V.tensor
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj U)
    (DerivedCategory.Q.obj ((coefficientTotalTensor.{u + 1, u + 1, u}
      (ProEt.topology Y) (ring l Y S)).obj (U, P)))
    (DerivedCategory.Q.obj (F.obj P)) (DerivedCategory.Q.obj U')
    (DerivedCategory.Q.obj ((coefficientTotalTensor.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R)).obj (U', F.obj P)))
    (C.models.iso _ _ _ U P hO hP) (A.models.iso _ _ _ U' (F.obj P) hO' hFP)
    (α.app P) (α.app U ≪≫ DerivedCategory.Q.mapIso V.unitCochain) c
    C.coherence.unitIso A.coherence.unitIso
    (DerivedCategory.Q.map bB.hom) (DerivedCategory.Q.map bA.hom) hm heB heA hf
  have hu0 : (ContinuousRational.derivedPull p O.coefficient).map
      C.coherence.unitIso.hom ≫ O.pullCounit.app U ≫
      DerivedCategory.Q.map V.unitCochain.hom = V.unit.hom ≫ A.coherence.unitIso.hom :=
    V.unit_representative
  have hu : (ContinuousRational.derivedPull p O.coefficient).map
      C.coherence.unitIso.hom ≫ O.pullCounit.app U ≫
      DerivedCategory.Q.map V.unitCochain.hom ≫ A.coherence.unitIso.inv = V.unit.hom := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫ A.coherence.unitIso.inv) hu0
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    α, asIso_hom, Category.assoc] at hh
  rw [hu] at hh
  exact hh

end WeilConjectures.AdicQbarRealization.Proper
