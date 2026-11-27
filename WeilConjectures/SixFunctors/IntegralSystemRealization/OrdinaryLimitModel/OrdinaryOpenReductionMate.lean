/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.OrdinaryOpenFiniteEvaluation
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.OrdinaryFiniteQuotientOpenSupport
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece

/-! # Ordinary open quotient comparison

## References

* [Stacks, Tag 03DI]
* [Stacks, Tag 03EK]
* [Stacks, Tag 0E8I]
* [Stacks, Tag 0941]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

local instance ordinaryReduction_additive (W : Scheme.{u}) :
    (pullbackTensorOrdinaryReduction l E W).Additive :=
  (pullbackTensorOrdinary_additive l E W).1

local instance actualOpen_additive {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).Additive :=
  (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j).left_adjoint_additive

/-- The ordinary quotient/open comparison, with its specified adjunction transpose. -/
def OrdinaryLimitModel.openReduction (a : OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (o : Open l E j) :
    pullbackTensorOrdinaryReduction l E X ⋙ o.ordinary ⟶
      PurCompactSupport.openExtension (PurCompactSupport.completed l E) j ⋙
        pullbackTensorOrdinaryReduction l E Y :=
  (mateEquiv (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j)
    o.adjunction).symm (a.reductionPull l E j).hom

/-- Degreewise ordinary mate, using the two separate complex functors. -/
def OrdinaryLimitModel.openReductionComplex (a : OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (o : Open l E j)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    (o.ordinary.mapHomologicalComplex (.up ℤ)).obj
        (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj
        ((Functor.mapHomologicalComplex
          (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j)
          (.up ℤ)).obj P) where
  f i := (a.openReduction l E j o).app (P.X i)
  comm' i k _ := ((a.openReduction l E j o).naturality (P.d i k)).symm

private theorem integralOpenUnit_isIso {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : scalarReductionSource l E X) :
    IsIso ((PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j).unit.app M) := by
  let R := PurCompactSupport.completed l E
  obtain ⟨e, ⟨h⟩⟩ := proEtaleOpen_slicePresentation j (R.ring Y) (R.ring X) (R.pull j)
  let L := SheafOfModules.localizedModuleExtension.{u} (R.ring Y) (ProEt.mk j)
  let adj := SheafOfModules.localizedModuleAdjunctionIndependent (R.ring Y) (ProEt.mk j)
  have := SheafOfModules.localizedUnit_isIso j (R.ring Y)
  have : L.Full := adj.fullyFaithfulLOfIsIsoUnit.full
  have : L.Faithful := adj.fullyFaithfulLOfIsIsoUnit.faithful
  have : e.functor.Full := e.fullyFaithfulFunctor.full
  have : e.functor.Faithful := e.fullyFaithfulFunctor.faithful
  have hfull : (e.functor ⋙ L).Full := Functor.Full.comp e.functor L
  have hfaithful : (e.functor ⋙ L).Faithful := Functor.Faithful.comp e.functor L
  have : (PurCompactSupport.openExtension R j).Full :=
    @Functor.Full.of_iso _ _ _ _ _ _ hfull h.symm
  have : (PurCompactSupport.openExtension R j).Faithful :=
    @Functor.Faithful.of_iso _ _ _ _ _ _ hfaithful h.symm
  let hu : IsIso (PurCompactSupport.openAdjunction R j).unit :=
    (PurCompactSupport.openAdjunction R j).unit_isIso_of_L_fully_faithful
  exact ((@asIso _ _ _ _ (PurCompactSupport.openAdjunction R j).unit hu).app M).isIso_hom

attribute [local irreducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

private theorem sequence_isIso_of_evaluation (W : Scheme.{u})
    {M N : coefficientSequenceModules l E W} (f : M ⟶ N)
    (hf : ∀ n : ℕ, IsIso ((coefficientSequenceEvaluation l E W n).map f)) : IsIso f := by
  let T := SheafOfModules.toSheaf
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E W)) ⋙
      sheafToPresheaf _ AddCommGrpCat.{u + 1}
  have : ∀ V, IsIso ((T.map f).app V) := by
    intro Z
    let n := Z.unop.1
    let V := Z.unop.2
    exact ((SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ AddCommGrpCat ⋙
      (CategoryTheory.evaluation _ _).obj (op V)).mapIso
        (@asIso _ _ _ _ ((coefficientSequenceEvaluation l E W n).map f) (hf n))).isIso_hom
  have : IsIso (T.map f) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso f T

/-- The ordinary scalar/open mate is invertible before localization. -/
theorem ordinaryOpenReduction_isIso (a : OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (o : Open l E j)
    (M : scalarReductionSource l E X) :
    IsIso ((a.openReduction l E j o).app M) := by
  let J := PurCompactSupport.openExtension (PurCompactSupport.completed l E) j
  let R := pullbackTensorOrdinaryReduction l E Y
  let N := R.obj (J.obj M)
  have hc : IsIso (o.adjunction.counit.app N) := by
    apply sequence_isIso_of_evaluation l E Y
    intro n
    obtain ⟨L, adj, e, he⟩ := ordinaryOpenFiniteEvaluation l E j o n
    let hquot : IsIso (adj.counit.app
        ((unrestrictedIntegralReductionFunctor l E Y n).obj (J.obj M))) :=
      ordinaryFiniteQuotientOpenSupport l E j n L adj M
    let hfin : IsIso (adj.counit.app ((coefficientSequenceEvaluation l E Y n).obj N)) :=
      (NatTrans.isIso_app_iff_of_iso adj.counit
        ((pullbackTensorReductionEvaluation l E Y n).app (J.obj M))).mp hquot
    rw [he]
    exact (e.app ((pullbackTensorSequenceInverse l E j).obj N) ≪≫
      L.mapIso ((pullbackTensorSequenceInverseEvaluation l E j n).app N).symm ≪≫
      @asIso _ _ _ _ (adj.counit.app ((coefficientSequenceEvaluation l E Y n).obj N))
        hfin).isIso_hom
  let hu := integralOpenUnit_isIso l E j M
  change IsIso
    (𝟙 _ ≫ o.ordinary.map
      ((pullbackTensorOrdinaryReduction l E X).map
        ((PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j).unit.app M)) ≫
      o.ordinary.map (𝟙 _) ≫
      o.ordinary.map ((a.reductionPull l E j).hom.app (J.obj M)) ≫
      o.ordinary.map (𝟙 _) ≫ o.adjunction.counit.app N ≫ 𝟙 _)
  exact (Iso.refl _ ≪≫ o.ordinary.mapIso ((pullbackTensorOrdinaryReduction l E X).mapIso
    (@asIso _ _ _ _
      ((PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j).unit.app M)
      hu)) ≪≫ o.ordinary.mapIso (Iso.refl _) ≪≫
      o.ordinary.mapIso ((a.reductionPull l E j).app (J.obj M)) ≪≫
      o.ordinary.mapIso (Iso.refl _) ≪≫
      @asIso _ _ _ _ (o.adjunction.counit.app N) hc ≪≫ Iso.refl _).isIso_hom

end WeilConjectures.IntegralSystemRealization
