/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenProperClopenWitness

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import WeilConjectures.AlgebraicGeometry.Bounded.BoundedComplexDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedRestrictionTestDetection
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenBoundaryTestHypercohomology
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationExact
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement

/-! # Boundary restriction of the higher direct image

Source: the proof plan of `isZero_higherDirectImage_open_injective_of_proper`
in `WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenInjectiveProperAcyclic`.
(blueprint: lem-sp-proetale-open-injective-proper-acyclic-boundary-restriction)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem evaluation_higherDirectImage
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (W : Y.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology Y) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (Opposite.op W))) (q : ℤ) :
    IsZero (((SheafOfModules.evaluation
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing Y A)) (Opposite.op W)) ⋙
        forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}).obj
      ((DerivedCategory.homologyFunctor _ q).obj
        ((proEtaleConstantDerivedDirectImage f A).obj (DerivedCategory.Q.obj K)))) ↔
      IsZero ((ProEt.ringHypercohomology X
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing X A)) ((proEtaleBaseChange f).obj W) q).obj K) := by
  let RX := (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X A)
  let RY := (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing Y A)
  let F := proEtaleConstantModuleDirectImage f A
  let E : proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤ AddCommGrpCat.{u + 1} :=
    SheafOfModules.evaluation.{u + 1} RY (Opposite.op W) ⋙
      forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}
  let : (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W)).PreservesHomology :=
    ProEt.weaklyContractible_evaluation_preservesHomology Y (proEtaleConstantRing Y A) W hW
  let : PreservesFiniteLimits (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W)) :=
    (ProEt.affine_weaklyContractible_evaluation_colimits Y (proEtaleConstantRing Y A) W hW).1
  let : PreservesFiniteLimits E := comp_preservesFiniteLimits
    (SheafOfModules.evaluation.{u + 1} RY (Opposite.op W))
    (forget₂ (ModuleCat.{u + 1} (RY.obj.obj (Opposite.op W))) AddCommGrpCat.{u + 1})
  let : E.PreservesEpimorphisms := by
    dsimp only [E]
    infer_instance
  let : E.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels E
  let I := (ProEt.ringModuleResolutionFunctor RX).obj K
  have : I.IsKInjective := (ProEt.ringModuleResolution_isKInjective_quasiIso RX K).1
  have : QuasiIso (ProEt.ringModuleResolutionMap RX K) :=
    (ProEt.ringModuleResolution_isKInjective_quasiIso RX K).2
  let e := F.rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map (ProEt.ringModuleResolutionMap RX K))) ≪≫
    F.rightDerivedFunctorObjQIso I
  let h := (DerivedCategory.homologyFunctorFactors _ q).app
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  let c := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q).mapIso
    (HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _)
      (by intros; rfl) :
      (E.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
        ((ProEt.ringModuleModelEvaluation RX ((proEtaleBaseChange f).obj W)).mapHomologicalComplex
          (.up ℤ)).obj ((ProEt.ringModuleModelResolutionFunctor RX).obj K))
  let : E.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (.up ℤ)).obj I).sc q) := inferInstance
  exact (E.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso e ≪≫ h) ≪≫
    ((((F.mapHomologicalComplex (.up ℤ)).obj I).sc q).mapHomologyIso E).symm ≪≫ c).isZero_iff

/-- Vanishing on the boundary part of the base open-closed decomposition.

Source: the recorded compactification-independence proof plan in
`WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenInjectiveProperAcyclic`, steps
4--7. Stacks Tag 0F7B is its etale analogue only.

Proof: Write F = k_!J and G = H^q(Rp_*F[0]). Apply the generic
closed-restriction detection theorem to G. It suffices to make G(W) zero for
each affine weakly contractible test W whose points specialize into the closed
complement. Choose the published functorial K-injective resolution of F[0].
The right-derived-functor comparison computes Rp_* on this resolution.
Exact evaluation at W commutes with its homology, while the sectionwise
pushforward formula identifies the evaluated complex with the one defining
hypercohomology on B times_D W. The local boundary-test hypercohomology lemma
makes its positive homology zero. The single-complex comparison transports
this vanishing to the specified DerivedCategory.singleFunctor input.
Closed-restriction detection then gives the conclusion. The local lemma retains
the arbitrary-injective calculation as its own obligation; the etale-origin-only
proper-boundary theorem is not applied.
(blueprint: lem-sp-proetale-open-injective-proper-acyclic-boundary-restriction)
-/
theorem isZero_boundaryRestriction_higherDirectImage_open_injective_of_proper
    (A : Type u) [CommRing A] [Finite A]
    {B D C E : Scheme.{u}} (p : B ⟶ D) (r : C ⟶ E)
    (k : C ⟶ B) (i : E ⟶ D)
    [IsProper p] [IsProper r]
    [IsOpenImmersion k] [QuasiCompact k]
    [IsOpenImmersion i] [QuasiCompact i]
    (hcomm : k ≫ p = r ≫ i)
    (J : proEtaleRingModules C (proEtaleConstantRing C A)) [Injective J]
    (w : OpenProperClopenWitness p r k i)
    (q : ℕ) (hq : 0 < q) :
    IsZero ((proEtaleConstantRingPullback A i.closedComplement).obj
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules D (proEtaleConstantRing D A)) (q : ℤ)).obj
        ((proEtaleConstantDerivedDirectImage p A).obj
          ((DerivedCategory.singleFunctor
            (proEtaleRingModules B (proEtaleConstantRing B A)) 0).obj
            ((sfIntrinsicExtensionByZero k A).obj J))))) := by
  let F := (sfIntrinsicExtensionByZero k A).obj J
  let K := (CochainComplex.singleFunctor
    (proEtaleRingModules B (proEtaleConstantRing B A)) 0).obj F
  let M := (proEtaleConstantDerivedDirectImage p A).obj
    ((DerivedCategory.singleFunctor _ 0).obj F)
  apply isZero_closedRestriction_of_boundary_tests A i
    ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj M)
  intro W ha hW hspecializes
  let : IsAffine W.left := ha
  have hhyper := isZero_properOpen_boundary_test_hypercohomology
    A p r k i hcomm J w W hW hspecializes q hq
  have heval := (evaluation_higherDirectImage A p K W hW (q : ℤ)).2 hhyper
  let E := SheafOfModules.evaluation
    ((sheafCompose (ProEt.topology D)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing D A)) (Opposite.op W) ⋙
      forget₂ (ModuleCat.{u + 1} _) AddCommGrpCat.{u + 1}
  let eSingle := (DerivedCategory.singleFunctorIsoCompQ
    (proEtaleRingModules B (proEtaleConstantRing B A)) 0).app F
  exact heval.of_iso
    (E.mapIso ((DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      ((proEtaleConstantDerivedDirectImage p A).mapIso eSingle)))

end AlgebraicGeometry.Scheme
