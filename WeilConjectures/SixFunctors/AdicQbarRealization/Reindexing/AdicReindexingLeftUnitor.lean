/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicTensorReindexing
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingUnitComplex
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitLeftRepresentatives
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitRightRepresentatives
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorCoherence

/-! # Left unitor for ordinary adic reindexing

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Project, Tags 03EK and 0FPT.
(blueprint: lem-sf-adic-reindexing-left-unitor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite WeilConjectures CategoryTheory.RingedForgetTensorTransposition
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
attribute [local irreducible] coefficientTotalTensor
  homComplexFunctor homComplexπ derivedInternalHomOfUniverses coefficientHomResolutionIso
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors DerivedCategory
  instCategoryDerivedCategory DerivedCategory.Q SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  {R : LocallyFiniteAdicRealization.Realization l X}
  {S : LocallyFiniteAdicRealization.Realization l Y}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  {A : At l X R} {B : At l Y S} {r : RingReindex l X g R S}
  (V : ReindexTensor l X g A B r)

attribute [local irreducible] tensorSummand

set_option maxHeartbeats 400000 in
-- Assemble the normalized K-flat model equations with their exact-derived factors.
/-- Ordinary adic reindexing preserves the left unitor for its recorded tensor and
coefficient-unit comparisons.

Source: BS Remark 6.8.15; Stacks 03EK and 0FPT.
(blueprint: lem-sf-adic-reindexing-left-unitor).

Proof: choose a K-flat representative P of M. The coefficient complex O is K-flat,
and the representative equation identifies the tensorator on (O,P). The two
left-unitor models are multiplication by the coefficient in degree zero.
On a homogeneous tensor, the pure reindexing equation preserves its two factors
and the unit-section equation applies the coefficient-ring map. Transport of the
module action uses the inverse ring map, so both composites multiply by the same
coefficient. All summands with a nonzero first degree vanish. Thus the chain unit
square commutes. Naturality of the tensor models and of the exact-derived
factorization gives the derived square; transport along Q(P) ≅ M finishes. -/
theorem reindexing_left_unitor (M : DerivedCategory (modules l Y S)) :
    V.tensor.hom.app (B.closed.monoidal.tensorUnit, M) ≫
      A.closed.tensor.map (Prod.mkHom (pullUnit l X g V).hom (𝟙 _)) ≫
      (A.closed.monoidal.leftUnitor ((derivedPull l X g r).obj M)).hom =
    (derivedPull l X g r).map (B.closed.monoidal.leftUnitor M).hom := by
  obtain ⟨P, hP, _, ⟨eM⟩⟩ :=
    flat_representative.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S) M
  apply left_unit_of_iso B.closed A.closed (derivedPull l X g r) V.tensor
    (pullUnit l X g V) eM
  let F := (modulePull l X g r).mapHomologicalComplex (.up ℤ)
  let O := ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)
  let O' := ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)
  have hO := unit_kflat.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)
  have hO' := unit_kflat.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)
  have hFP := V.kflat P hP
  have hFO := V.kflat O hO
  obtain ⟨bB, hbB, heB⟩ := B.coherence.leftUnitor_model P hP
  obtain ⟨bA, hbA, heA⟩ := A.coherence.leftUnitor_model (F.obj P) hFP
  rw [B.coherence.tensorIso_both O P hO hP] at heB
  rw [A.coherence.tensorIso_both O' (F.obj P) hO' hFP] at heA
  have hc := reindexing_left_unitor_chain l g V P bB bA hbB hbA
  let α := (modulePull l X g r).mapDerivedCategoryFactors
  let t := (coefficientTotalTensor.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R)).mapIso
      (V.unitCochain.prod (Iso.refl (F.obj P)))
  let c := α.app ((coefficientTotalTensor.{u + 1, u + 1, u}
    (ProEt.topology Y) (ring l Y S)).obj (O, P)) ≪≫
    DerivedCategory.Q.mapIso (V.cochain.app (O, P)) ≪≫ DerivedCategory.Q.mapIso t
  have hm : (derivedPull l X g r).map (B.models.iso _ _ _ O P hO hP).hom ≫
      V.tensor.hom.app (DerivedCategory.Q.obj O, DerivedCategory.Q.obj P) ≫
      A.closed.tensor.map
        (X := ((derivedPull l X g r).obj (DerivedCategory.Q.obj O),
          (derivedPull l X g r).obj (DerivedCategory.Q.obj P)))
        (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
        ((α.app O ≪≫ DerivedCategory.Q.mapIso V.unitCochain).hom, (α.app P).hom) =
      c.hom ≫ (A.models.iso _ _ _ O' (F.obj P) hO' hFP).hom := by
    have hm := V.representative O P hO hP
    have hn := A.coherence.tensorIso_naturality (F.obj O) (F.obj P) O' (F.obj P)
      (Or.inr hFP) (Or.inr hFP) V.unitCochain.hom (𝟙 _)
    rw [A.coherence.tensorIso_both _ _ hFO hFP,
      A.coherence.tensorIso_both _ _ hO' hFP] at hn
    let := A.closed.monoidal
    calc
      _ = (derivedPull l X g r).map (B.models.iso _ _ _ O P hO hP).hom ≫
          V.tensor.hom.app (DerivedCategory.Q.obj O, DerivedCategory.Q.obj P) ≫
          A.closed.tensor.map
            (X := ((derivedPull l X g r).obj (DerivedCategory.Q.obj O),
              (derivedPull l X g r).obj (DerivedCategory.Q.obj P)))
            (Y := (DerivedCategory.Q.obj (F.obj O), DerivedCategory.Q.obj (F.obj P)))
            ((α.app O).hom, (α.app P).hom) ≫
          A.closed.tensor.map
            (X := (DerivedCategory.Q.obj (F.obj O), DerivedCategory.Q.obj (F.obj P)))
            (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
            (DerivedCategory.Q.map V.unitCochain.hom, 𝟙 _) := by
        simp only [Iso.trans_hom, Functor.mapIso_hom, CoefficientClosedStructure.tensor,
          tensor_map, tensorHom_comp_tensorHom, Category.comp_id]
      _ = (α.app _).hom ≫ DerivedCategory.Q.map (V.cochain.hom.app (O, P)) ≫
          (A.models.iso _ _ _ (F.obj O) (F.obj P) hFO hFP).hom ≫
          A.closed.tensor.map
            (X := (DerivedCategory.Q.obj (F.obj O), DerivedCategory.Q.obj (F.obj P)))
            (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
            (DerivedCategory.Q.map V.unitCochain.hom, 𝟙 _) := by
        simpa only [Category.assoc, α, F, Iso.app_hom] using
          congrArg (fun f ↦ f ≫ A.closed.tensor.map
            (X := (DerivedCategory.Q.obj (F.obj O), DerivedCategory.Q.obj (F.obj P)))
            (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
            (DerivedCategory.Q.map V.unitCochain.hom, 𝟙 _)) hm
      _ = _ := by
        have hn' : DerivedCategory.Q.map t.hom ≫
            (A.models.iso _ _ _ O' (F.obj P) hO' hFP).hom =
            (A.models.iso _ _ _ (F.obj O) (F.obj P) hFO hFP).hom ≫
              A.closed.tensor.map
                (X := (DerivedCategory.Q.obj (F.obj O), DerivedCategory.Q.obj (F.obj P)))
                (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
                (DerivedCategory.Q.map V.unitCochain.hom, 𝟙 _) := by
          have hn0 : DerivedCategory.Q.map t.hom ≫
              (A.models.iso _ _ _ O' (F.obj P) hO' hFP).hom =
              (A.models.iso _ _ _ (F.obj O) (F.obj P) hFO hFP).hom ≫
                A.closed.tensor.map
                  (X := (DerivedCategory.Q.obj (F.obj O), DerivedCategory.Q.obj (F.obj P)))
                  (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
                  (DerivedCategory.Q.map V.unitCochain.hom,
                    DerivedCategory.Q.map (𝟙 (F.obj P))) := by
            simpa only [t, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
              Prod.mkHom, F, O'] using hn
          exact hn0.trans (congrArg (fun f ↦
            (A.models.iso _ _ _ (F.obj O) (F.obj P) hFO hFP).hom ≫
              A.closed.tensor.map
                (X := (DerivedCategory.Q.obj (F.obj O), DerivedCategory.Q.obj (F.obj P)))
                (Y := (DerivedCategory.Q.obj O', DerivedCategory.Q.obj (F.obj P)))
                (DerivedCategory.Q.map V.unitCochain.hom, f))
            (DerivedCategory.Q.map_id (F.obj P)))
        simpa only [c, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
          Category.assoc] using
          congrArg (fun f ↦ (α.app _).hom ≫
            DerivedCategory.Q.map (V.cochain.hom.app (O, P)) ≫ f) hn'.symm
  have hf : (derivedPull l X g r).map (DerivedCategory.Q.map bB.hom) ≫
      (α.app P).hom = c.hom ≫ DerivedCategory.Q.map bA.hom := by
    have hn := α.hom.naturality bB.hom
    change (derivedPull l X g r).map (DerivedCategory.Q.map bB.hom) ≫ (α.app P).hom =
      (α.app _).hom ≫ DerivedCategory.Q.map (F.map bB.hom) at hn
    rw [hn, hc]
    simp only [Functor.map_comp, c, Iso.trans_hom, Functor.mapIso_hom,
      t, Iso.prod_hom, Iso.refl_hom, Iso.app_hom, Prod.mkHom, Category.assoc, O, F]
  have hh := left_unit_of_models B.closed A.closed (derivedPull l X g r) V.tensor
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj O)
    (DerivedCategory.Q.obj ((coefficientTotalTensor.{u + 1, u + 1, u}
      (ProEt.topology Y) (ring l Y S)).obj (O, P)))
    (DerivedCategory.Q.obj (F.obj P)) (DerivedCategory.Q.obj O')
    (DerivedCategory.Q.obj ((coefficientTotalTensor.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R)).obj (O', F.obj P)))
    (B.models.iso _ _ _ O P hO hP) (A.models.iso _ _ _ O' (F.obj P) hO' hFP)
    (α.app P) (α.app O ≪≫ DerivedCategory.Q.mapIso V.unitCochain) c
    B.coherence.unitIso A.coherence.unitIso
    (DerivedCategory.Q.map bB.hom) (DerivedCategory.Q.map bA.hom) hm heB heA hf
  simpa only [pullUnit, α, F, O, Iso.trans_assoc] using hh

end WeilConjectures.AdicQbarRealization
