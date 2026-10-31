/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData
public import WeilConjectures.AlgebraicGeometry.CompactSupportNativeSystemEvaluation
import all WeilConjectures.AlgebraicGeometry.NativeConstantRestrictionAcyclicity
import WeilConjectures.AlgebraicGeometry.NativeConstantSupportModel
import all WeilConjectures.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage

/-! # Ordinary quotient-module operations determined by scalar restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

open NativeConstantModel

private theorem quotient_surjective (W : Scheme.{u}) (n : ℕ) :
    Presheaf.IsLocallySurjective (ProEt.topology W) (quotient l E W n).hom := by
  let q : CommRingCat.of (coefTraceRing l E) ⟶
      CommRingCat.of (finiteDualizingCoeff l E n) :=
    CommRingCat.ofHom (coefTraceQuotient l E n)
  let k := (Functor.const W.ProEtᵒᵖ).map q
  have : Presheaf.IsLocallySurjective (ProEt.topology W) k := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro V a
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective a.down
    exact ⟨ULift.up r, congrArg ULift.up hr⟩
  have h := (sheafificationAdjunction (ProEt.topology W) CommRingCat.{u + 1}).unit.naturality k
  apply Presheaf.isLocallySurjective_of_isLocallySurjective_fac (ProEt.topology W)
    (f₁ := toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj _))
    (f₃ := k ≫ toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj _))
  exact h.symm

private theorem sequenceScalar_surjective (W : Scheme.{u}) :
    Presheaf.IsLocallySurjective (coefficientSequenceTopology (ProEt.topology W))
      (scalarMap l E W).hom := by
  constructor
  intro U x
  have := quotient_surjective l E W U.1
  change (Presheaf.imageSieve (scalarMap l E W).hom x).functorPullback
    (Prod.sectR U.1 W.ProEt) ∈ (ProEt.topology W) U.2
  apply (ProEt.topology W).superset_covering _
    (Presheaf.imageSieve_mem (ProEt.topology W) (quotient l E W U.1).hom x)
  intro V g hg
  obtain ⟨t, ht⟩ := hg
  refine ⟨t, ?_⟩
  change (quotient l E W U.1).hom.app (op V) t =
    (((coefficientSequenceCommRingSystem l E W).map (𝟙 (op U.1))).hom.app (op U.2) ≫
      ((coefficientSequenceCommRingSystem l E W).obj (op U.1)).obj.map g.op) x
  have hi := congrArg (fun k ↦ (k.hom.app (op U.2) ≫
    ((coefficientSequenceCommRingSystem l E W).obj (op U.1)).obj.map g.op) x)
      ((coefficientSequenceCommRingSystem l E W).map_id (op U.1))
  exact ht.trans hi.symm

private def nativeRestrictionFullyFaithful (W : Scheme.{u}) :
    (nativeRestriction l E W).FullyFaithful := by
  have hs := sequenceScalar_surjective l E W
  have : Presheaf.IsLocallySurjective (coefficientSequenceTopology (ProEt.topology W))
      (((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarMap l E W)).hom) :=
    ⟨hs.imageSieve_mem⟩
  have hf : (nativeScalarRestriction l E W).Full :=
    { map_surjective := fun {M N} f ↦ by
        refine ⟨⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
        (((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarMap l E W)).hom)
            N.isSheaf).symm f.val⟩, ?_⟩
        ext V x
        rfl }
  have hfai : (nativeScalarRestriction l E W).Faithful :=
    { map_injective := fun {M N} f g h ↦ by
        ext V x
        exact congrArg (fun k ↦ k.val.app V x) h }
  let ff := (Functor.FullyFaithful.ofFullyFaithful (nativeScalarRestriction l E W)).comp
    ((sequenceEquivalence (ProEt.topology W)
      (integralConstantRingOfUniverses l E W)).fullyFaithfulFunctor)
  let e := Classical.choice (restrictionTower l E W)
  exact ff.ofIso e

private def traceConstantComparison (W : Scheme.{u}) :
    coefTraceConstantScalars l E W ≅
      PurStrictScalar.constantRestriction l E W ⋙
        ProEtale.scalarSectionsAt W (coefTraceRing l E) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ ?_) ?_)) ?_
  · refine (show ((coefTraceConstantScalars l E W).obj M).obj.obj V ≃ₗ[coefTraceRing l E]
        (((PurStrictScalar.constantRestriction l E W ⋙
          ProEtale.scalarSectionsAt W (coefTraceRing l E)).obj M).obj.obj V) from
      { toFun := id
        invFun := id
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a x ↦ ?_ }).toModuleIso
    let b := (integralConstantToCompletionOfUniverses l E W).hom
    let η := Functor.whiskerRight (toSheafify (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (coefTraceRing l E))))
      (forget₂ CommRingCat RingCat)
    let v := (MorphismProperty.Over.mkIdTerminal _ _).op.to V
    have hb := congrArg (fun z ↦ z (η.app (op (ProEt.mk (𝟙 W))) a)) (b.naturality v)
    have hη := congrArg (fun z ↦ z a) (η.naturality v)
    change (((completedIntegralCoefficientSheafUnrestricted l E W).obj.map v)
      (b.app (op (ProEt.mk (𝟙 W))) (η.app (op (ProEt.mk (𝟙 W))) a))) •
        (show M.val.obj V from x) = b.app V (η.app V a) • (show M.val.obj V from x)
    exact congrArg (fun r : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj V ↦
      r • (show M.val.obj V from x)) (hb.symm.trans (congrArg (b.app V) hη.symm))
  · intros
    ext x
    rfl
  · intros
    ext V x
    rfl

private abbrev traceEncoding (W : Scheme.{u}) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (ProEtale.scalarSectionsAt W (coefTraceRing l E))

private def traceSystemComparison (W : Scheme.{u}) :
    coefTraceSystemRestriction l E W ≅
      PurStrictScalar.systemRestriction l E W ⋙ traceEncoding l E W :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun n ↦ (traceConstantComparison l E W).app
      (((coefficientSequenceRestriction l E W).obj M).obj n))
    (fun f ↦ (traceConstantComparison l E W).hom.naturality
      (((coefficientSequenceRestriction l E W).obj M).map f))) (by
        intro M N f
        apply NatTrans.ext
        funext n
        exact (traceConstantComparison l E W).hom.naturality
          (((coefficientSequenceRestriction l E W).map f).app n))

private def traceRestrictionFullyFaithful (W : Scheme.{u}) :
    (coefTraceSystemRestriction l E W).FullyFaithful := by
  have := ProEtale.scalarSectionsAt_equiv W (coefTraceRing l E)
  exact ((nativeRestrictionFullyFaithful l E W).comp
    ((Functor.FullyFaithful.ofFullyFaithful
      (ProEtale.scalarSectionsAt W (coefTraceRing l E))).whiskeringRight ℕᵒᵖ)).ofIso
        (traceSystemComparison l E W).symm

private def encodingDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtale.StrictTower.moduleDirectImage (coefTraceRing l E) f ⋙
        ProEtale.scalarSectionsAt Y (coefTraceRing l E) ≅
      ProEtale.scalarSectionsAt X (coefTraceRing l E) ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (coefTraceRing l E)) f := by
  apply ProEtale.scalarDirectImageIso
  have hr : proEtaleRingDirectImageMap f
      (ProEtale.StrictTower.coefficients (coefTraceRing l E) Y)
      (ProEtale.StrictTower.coefficients (coefTraceRing l E) X)
      (ProEtale.StrictTower.constantRingIso (coefTraceRing l E) f) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (coefTraceRing l E)) :=
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  rw [hr]
  have h := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (coefTraceRing l E)))
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (ProEtale.scalarRing (ProEt.topology X) (coefTraceRing l E))))
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (coefTraceRing l E)))))
  exact congrArg (fun t ↦ Functor.whiskerRight t
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h

private def encodingAdjointSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (E : A ≌ C) (F : B ≌ D) {L : A ⥤ B} {R : B ⥤ A}
    {l : C ⥤ D} {r : D ⥤ C} (a : L ⊣ R) (b : l ⊣ r)
    (e : R ⋙ E.functor ≅ F.functor ⋙ r) :
    L ⋙ F.functor ≅ E.functor ⋙ l := by
  let d : F.inverse ⋙ R ⋙ E.functor ≅ r :=
    Functor.isoWhiskerLeft F.inverse e ≪≫ Functor.isoWhiskerRight F.counitIso r
  let h : E.inverse ⋙ L ⋙ F.functor ≅ l :=
    ((E.symm.toAdjunction.comp (a.comp F.toAdjunction)).ofNatIsoRight d).leftAdjointUniq b
  exact Functor.isoWhiskerRight E.unitIso (L ⋙ F.functor) ≪≫
    Functor.isoWhiskerLeft E.functor h

private def encodingOpen {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    ProEtale.StrictTower.moduleJ (coefTraceRing l E) j ⋙
        ProEtale.scalarSectionsAt Y (coefTraceRing l E) ≅
      ProEtale.scalarSectionsAt X (coefTraceRing l E) ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (coefTraceRing l E)) j := by
  have := ProEtale.scalarSectionsAt_equiv X (coefTraceRing l E)
  have := ProEtale.scalarSectionsAt_equiv Y (coefTraceRing l E)
  let ex := (ProEtale.scalarSectionsAt X (coefTraceRing l E)).asEquivalence
  let ey := (ProEtale.scalarSectionsAt Y (coefTraceRing l E)).asEquivalence
  let ep := encodingAdjointSquare ey ex
    (proEtaleRingModuleAdjunction j
      (ProEtale.StrictTower.coefficients (coefTraceRing l E) Y)
      (ProEtale.StrictTower.coefficients (coefTraceRing l E) X)
      (ProEtale.StrictTower.constantRingIso (coefTraceRing l E) j))
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (coefTraceRing l E)) j) (encodingDirect l E j)
  exact encodingAdjointSquare ex ey (ProEtale.StrictTower.moduleJAdj (coefTraceRing l E) j)
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (coefTraceRing l E)) j)
    ep

private def towerSquare {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (P : A ⥤ B) (F : B ⥤ D) (E : A ⥤ C) (Q : C ⥤ D)
    (e : P ⋙ F ≅ E ⋙ Q) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj P ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj F ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj E ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj Q :=
  Functor.whiskeringRightObjCompIso P F ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e ≪≫
      (Functor.whiskeringRightObjCompIso E Q).symm

private def traceNativeDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) f ⋙ coefTraceSystemRestriction l E Y ≅
      coefTraceSystemRestriction l E X ⋙ coefTracePush l E f :=
  Functor.isoWhiskerLeft _ (traceSystemComparison l E Y) ≪≫
    Functor.isoWhiskerRight (PurStrictScalar.systemProperOrdinary l E f)
      (traceEncoding l E Y) ≪≫
    Functor.isoWhiskerLeft (PurStrictScalar.systemRestriction l E X)
      (towerSquare _ _ _ _ (encodingDirect l E f)) ≪≫
    Functor.isoWhiskerRight (traceSystemComparison l E X).symm (coefTracePush l E f)

private def traceNativeOpen {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j ⋙ coefTraceSystemRestriction l E Y ≅
      coefTraceSystemRestriction l E X ⋙ coefTraceOpen l E j := by
  have := PurStrictScalar.systemOpenMap_isIso l E j
  exact Functor.isoWhiskerLeft _ (traceSystemComparison l E Y) ≪≫
    Functor.isoWhiskerRight (asIso (PurStrictScalar.systemOpenMap l E j)).symm
      (traceEncoding l E Y) ≪≫
    Functor.isoWhiskerLeft (PurStrictScalar.systemRestriction l E X)
      (towerSquare _ _ _ _ (encodingOpen l E j)) ≪≫
    Functor.isoWhiskerRight (traceSystemComparison l E X).symm (coefTraceOpen l E j)

set_option linter.unusedVariables false in
/-- The ordinary open and proper functors of a pairing system are the native
quotient-module operations.

Source: prop-coef-integral-dualizing, second proof paragraph, scalar restriction
before taking compact support; Stacks 03DI and 03D2.
(blueprint: lem-coef-pairing-native-operations).

Proof: at each positive level, restriction from the constant quotient ring sheaf
A_n to constant R-module sheaves is fully faithful. A map linear over R is linear
over A_n: locally every section of the quotient ring lifts to a constant R scalar,
and sheaf separatedness descends the scalar law. The same argument for each
vertical slice, with the existing horizontal maps, proves full faithfulness for
strict systems. Native open extension commutes with this restriction by its
extension-by-zero adjunction, and native direct image does so by its section
formula. Compose these restriction comparisons with G.openRestriction and
G.properRestriction, and lift the resulting natural isomorphisms through the
fully faithful restriction functors. Naturality and both inverse equations are
reflected by faithfulness. These are comparisons of ordinary functors, before
localizing or taking inverse limits. The proof includes the zero module, empty
open, identity maps, and the first quotient. -/
theorem coefPairing_native_operations
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus l E X) (G : CoefPairingSystem l E c S) :
    ∃ (j : G.openModules ≅ ProEtale.VaryingRing.extension
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) c.i),
      Nonempty (G.properModules ≅ ProEtale.VaryingRing.push
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) c.g) := by
  let ffZ := traceRestrictionFullyFaithful l E c.Z
  let ffY := traceRestrictionFullyFaithful l E Y
  let := ffZ.full
  let := ffZ.faithful
  let := ffY.full
  let := ffY.faithful
  exact ⟨Functor.fullyFaithfulCancelRight (coefTraceSystemRestriction l E c.Z)
    (G.openRestriction ≪≫ (traceNativeOpen l E c.i).symm),
    ⟨Functor.fullyFaithfulCancelRight (coefTraceSystemRestriction l E Y)
      (G.properRestriction ≪≫ (traceNativeDirect l E c.g).symm)⟩⟩

end WeilConjectures
