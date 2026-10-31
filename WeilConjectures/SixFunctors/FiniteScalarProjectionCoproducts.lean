/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData
import WeilConjectures.SixFunctors.FiniteTensorTestEtaleOrigin
import WeilConjectures.SixFunctors.CoefPairingSectionsLeftEvaluation
import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarCoproducts

/-! # Coproducts through finite proper scalar projection

Source: the scalar-generator proof of the finite proper projection formula.
(blueprint: lem-coef-finite-scalar-projection-coproducts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u})

private def scalarEvaluationLeftEvaluation (n : ℕ) :
    coefPairingEvaluationLeft l E n ⋙ coefPairingDerivedEvaluation l E n ≅ 𝟭 _ := by
  let A := ModuleCat.{u + 1} (coefTraceRing l E)
  let L := evaluationLeftAdjoint A (op n)
  let V := (evaluation ℕᵒᵖ A).obj (op n)
  letI : Unique (op n ⟶ op n) := ⟨⟨𝟙 _⟩, fun _ ↦ Subsingleton.elim _ _⟩
  letI := (evaluationAdjunctionRight A (op n)).isLeftAdjoint
  let e : L ⋙ V ≅ 𝟭 A := NatIso.ofComponents
    (fun M ↦ coproductUniqueIso (fun _ : op n ⟶ op n ↦ M)) (by
      intro M N f
      apply Sigma.hom_ext
      intro i
      simp [L, V, evaluationLeftAdjoint])
  exact (Functor.mapDerivedCategoryCompIso L V).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A

private def intrinsicOpenIso (A : Type u) [CommRing A] [Finite A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence U A).functor ⋙
        (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Z A).functor :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((sfIntrinsicModuleEquivalence U A).funInvIdAssoc
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
          (sfIntrinsicModuleEquivalence Z A).functor)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private theorem intrinsic_preserves_coproduct
    (A : Type u) [CommRing A] [Finite A] {k : Type u} [Field k]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (aZ : Z ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hp : p ≫ aY = aZ)
    {I : Type (u + 1)} (K : I → proEtaleDerivedCategory Z A)
    (hK : ∀ i, ProEtale.DerivedCategory.etaleOriginHomology (ULift.{u + 1, u} A) Z
      ((sfIntrinsicDerivedEquivalence Z A).inverse.obj (K i))) :
    PreservesColimit (Discrete.functor K) (proEtaleConstantDerivedDirectImage p A) := by
  let EZ := sfIntrinsicDerivedEquivalence Z A
  let EY := sfIntrinsicDerivedEquivalence Y A
  let N := fun i ↦ EZ.inverse.obj (K i)
  let R := (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor
  have : IsIso (sigmaComparison R N) :=
    ProEtale.isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology
      (ULift.{u + 1, u} A) p aZ aY hp N hK
  have : PreservesColimit (Discrete.functor N) R :=
    PreservesCoproduct.of_iso_comparison R N
  let P := proEtaleConstantDerivedDirectImage p A
  let β : EZ.functor ⋙ P ≅ R ⋙ EY.functor :=
    sfIntrinsicDerivedDirectImageComparison p A
  have : PreservesColimit (Discrete.functor N) (EZ.functor ⋙ P) :=
    preservesColimit_of_natIso (Discrete.functor N) β.symm
  let c : Cofan N := Cofan.mk (∐ N) (Sigma.ι N)
  have hc : IsColimit c := coproductIsCoproduct N
  have : PreservesColimit (Discrete.functor N ⋙ EZ.functor) P :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves EZ.functor hc)
      (isColimitOfPreserves (EZ.functor ⋙ P) hc)
  exact preservesColimit_of_iso_diagram P
    (Discrete.natIso (F := Discrete.functor N ⋙ EZ.functor)
      (G := Discrete.functor K) (fun i ↦ EZ.counitIso.app (K i.as)))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

include hl in
set_option linter.unusedSectionVars false in
/-- Proper image commutes with coproducts on the scalar family tensored with an
open-extended finite-Tor constructible input. This asserts no projection formula.
Source: Stacks 07A4, 0941; the truncation and scalar-generator argument of
lem-amb-proper-coproducts-projection.
(blueprint: lem-coef-finite-scalar-projection-coproducts).

Proof: finite evaluation of the representable scalar test is the identity,
since its indexing endomorphism type has just the identity arrow. Apply the
sections-left-evaluation comparison to the full source test pullbacks, and use
the tensor-evaluation and reduction comparisons of S. The existing finite-test
etale-origin theorem then supplies an etale model of the finite tensor test.
The frame's openTensor isomorphism identifies its extension by zero with the
compactified tensor family. Deriving the coefficient equivalence counit gives
the open-realization comparison, so every member has etale-origin cohomology.
Apply the source proper coproduct theorem to the inverse-realized family, and
transport its colimit cofan through the canonical derived direct-image comparison
and equivalence counit. Finally, scalar pullbacks and fixed tensor preserve
coproducts by their adjunctions. The argument covers empty families and zero inputs. -/
theorem finiteScalarProjection_preservesCoproducts
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (q : ℕ) (F : CoefPairingFiniteFrame l E (finiteDualizingCompactification D X) S G q)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : finiteTorConstructibleIntegral l E X K) :
    let c := finiteDualizingCompactification D X
    let P := proEtaleConstantDerivedDirectImage c.g
      (Padic.coefficientExtensionRing l E (q + 1))
    let M := (sfIntrinsicExtensionByZero c.i
      (Padic.coefficientExtensionRing l E (q + 1))).mapDerivedCategory.obj
        ((coefficientFiniteDerivedExtension l E X q).obj K)
    ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (F.sstar ⋙ F.pstar ⋙ Prod.sectL _ M ⋙
        (G.compactTensors.finiteClosed q).tensor ⋙ P) := by
  dsimp only
  let c := finiteDualizingCompactification D X
  let A := Padic.coefficientExtensionRing l E (q + 1)
  let EZ := sfIntrinsicDerivedEquivalence c.Z A
  let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
  let Kr := (coefficientFiniteDerivedExtension l E X q).obj K
  let M := J.obj Kr
  let C := G.compactTensors.finiteClosed q
  let Q := F.sstar ⋙ F.pstar ⋙ Prod.sectL _ M ⋙ C.tensor
  obtain ⟨e⟩ := coefPairing_sections_left_evaluation l E X
    (G.frame.testPull S.systemClosed G.baseTensors.systemClosed)
    G.frame.sourceAdjunction q
    (F.testPull (S.finiteClosed q) (G.baseTensors.finiteClosed q)) F.sourceAdjunction
  have hQ (T : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) :
      ProEtale.DerivedCategory.etaleOriginHomology (ULift.{u + 1, u} A) c.Z
        (EZ.inverse.obj (Q.obj T)) := by
    obtain ⟨H, ⟨hH⟩⟩ := integralDualizingFiniteTest_etaleOrigin D l E X S G K hK q T
    let eT := e.app ((coefPairingEvaluationLeft l E q).obj T) ≪≫
      (F.testPull (S.finiteClosed q) (G.baseTensors.finiteClosed q)).mapIso
        ((scalarEvaluationLeftEvaluation l E q).app T)
    let eTensor := (S.evaluationTensor q).app
      ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
        ((coefPairingEvaluationLeft l E q).obj T), S.reduction.obj K) ≪≫
      (S.finiteClosed q).tensor.mapIso
        (eT.prod ((S.reductionEvaluation q).app K))
    let N := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj H
    let V := (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory
    let r : EZ.functor.obj (V.obj N) ≅ Q.obj T :=
      (intrinsicOpenIso A c.i).symm.app N ≪≫
        J.mapIso (hH ≪≫ eTensor) ≪≫
        F.openTensor (F.pstar.obj (F.sstar.obj T)) Kr
    exact (ProEtale.DerivedCategory.etaleOriginHomology
      (ULift.{u + 1, u} A) c.Z).prop_of_iso
        (EZ.unitIso.app (V.obj N) ≪≫ EZ.inverse.mapIso r)
        (ProEtale.DerivedCategory.etaleOriginHomology_openImmersionLowerShriek
          (ULift.{u + 1, u} A) c.Z c.i
          (ProEtale.DerivedCategory.etaleOriginHomology_mapDerivedCategory_obj H))
  let := F.sectionsAdjunction.isLeftAdjoint
  let := F.properAdjunction.isLeftAdjoint
  let := C.monoidal
  let eM : (Prod.sectL _ M ⋙ C.tensor) ≅ MonoidalCategory.tensorRight M :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro N N' f
      simp [CoefficientClosedStructure.tensor, MonoidalCategory.tensor,
        MonoidalCategory.tensorRight, Prod.sectL])
  let := ((C.adjunction M).ofNatIsoLeft eM.symm).isLeftAdjoint
  have hQc (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) Q := by
    change PreservesColimitsOfShape (Discrete I)
      ((F.sstar ⋙ F.pstar) ⋙ (Prod.sectL _ M ⋙ C.tensor))
    infer_instance
  intro I
  have := hQc I
  have hT (T : I → DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) :
      PreservesColimit (Discrete.functor T)
        (Q ⋙ proEtaleConstantDerivedDirectImage c.g A) := by
    have : PreservesColimit (Discrete.functor T ⋙ Q)
        (proEtaleConstantDerivedDirectImage c.g A) := by
      have := intrinsic_preserves_coproduct A c.g c.g (𝟙 _) (Category.comp_id _)
        (fun i ↦ Q.obj (T i)) (fun i ↦ hQ (T i))
      exact preservesColimit_of_iso_diagram _
        (Discrete.natIso (F := Discrete.functor (fun i ↦ Q.obj (T i)))
          (G := Discrete.functor T ⋙ Q) (fun _ ↦ Iso.refl _))
    infer_instance
  let := hT
  exact preservesColimitsOfShape_of_discrete
    (Q ⋙ proEtaleConstantDerivedDirectImage c.g A)

end WeilConjectures
