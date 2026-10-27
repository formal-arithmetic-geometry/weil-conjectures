/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.IntegralSupportNormalizationData
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-! # Whole-system normalization of the open Hom transpose

Source: smooth-purity localization, the open adjunction and Hom vanishing paragraphs;
Stacks 03DI, 0941 and 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSupportNormalization

private def reductionFullyFaithful
    {C D : Type*} [Category C] [Category D] (P : ObjectProperty C)
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (hu : ∀ K : P.FullSubcategory, IsIso (adj.unit.app K.obj)) :
    (P.ι ⋙ F).FullyFaithful := by
  let (K : P.FullSubcategory) := hu K
  exact
    { preimage := fun {K L} f ↦ ⟨adj.homEquiv _ _ f ≫ inv (adj.unit.app L.obj)⟩
      map_preimage := by
        intro K L f
        change F.map (adj.homEquiv _ _ f ≫ inv (adj.unit.app L.obj)) = f
        have he : F.map (inv (adj.unit.app L.obj)) = adj.counit.app (F.obj L.obj) := by
          apply (cancel_epi (F.map (adj.unit.app L.obj))).1
          rw [← Functor.map_comp]
          simp
        rw [Functor.map_comp, he]
        exact (adj.homEquiv _ _).symm_apply_apply f
      preimage_map := by
        intro K L f
        ext
        change adj.homEquiv _ _ (F.map f.hom) ≫ inv (adj.unit.app L.obj) = f.hom
        rw [Adjunction.homEquiv_unit]
        change (adj.unit.app K.obj ≫ (F ⋙ G).map f.hom) ≫ _ = _
        rw [← adj.unit.naturality f.hom]
        simp }

private theorem normalizeRestriction
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {iC : C ⥤ C'} {iD : D ⥤ D'} (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
    {L : C ⥤ D} {R R₀ : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (a' : L' ⊣ R')
    (d : L ⋙ iD ≅ iC ⋙ L') (q : R₀ ⋙ iC ≅ iD ⋙ R') :
    ∃ p : R ⋙ iC ≅ iD ⋙ R',
      a'.restrictFullyFaithful hiC hiD d.symm p.symm = a := by
  let b := a'.restrictFullyFaithful hiC hiD d.symm q.symm
  let e := a.rightAdjointUniq b
  let p := isoWhiskerRight e iC ≪≫ q
  refine ⟨p, ?_⟩
  apply Adjunction.ext
  apply NatTrans.ext
  funext K
  apply hiC.map_injective
  have hu := a.unit_rightAdjointUniq_hom_app b K
  change a.unit.app K ≫ e.hom.app (L.obj K) = b.unit.app K at hu
  have hu' : b.unit.app K ≫ e.inv.app (L.obj K) = a.unit.app K := by
    rw [← hu, Category.assoc, e.hom_inv_id_app]
    exact Category.comp_id (a.unit.app K)
  rw [a'.map_restrictFullyFaithful_unit_app]
  change a'.unit.app (iC.obj K) ≫ R'.map (d.inv.app K) ≫
    (q.inv.app (L.obj K) ≫ iC.map (e.inv.app (L.obj K))) = _
  have hb : iC.map (b.unit.app K) =
      a'.unit.app (iC.obj K) ≫ R'.map (d.inv.app K) ≫ q.inv.app (L.obj K) := by
    exact a'.map_restrictFullyFaithful_unit_app hiC hiD d.symm q.symm K
  calc
    _ = (a'.unit.app (iC.obj K) ≫ R'.map (d.inv.app K) ≫
        q.inv.app (L.obj K)) ≫ iC.map (e.inv.app (L.obj K)) := by
      simp only [Category.assoc]
    _ = iC.map (b.unit.app K) ≫ iC.map (e.inv.app (L.obj K)) := by rw [hb]
    _ = _ := by rw [← iC.map_comp, hu']


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Transport the recorded recollement pullback across the unique module adjoint. -/
private theorem ordinaryOpenPull_constructible (D : FiniteFieldDatum.{u})
    (primeUnit : IsUnit (l : D.k))
    {U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] :
    ∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E U ((ordinaryOpenPull l E j).obj K.obj) := by
  let R := (PurCompactSupport.completed l E).ring X
  let S := (PurCompactSupport.completed l E).ring U
  let c := (PurCompactSupport.completed l E).pull j
  have hc : proEtaleRingDirectImageMap j R S c = sfCompletedCoefficientMap l E j := by
    change (proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _).symm
        (sfCompletedCoefficientMap l E j)) = _
    exact Equiv.apply_symm_apply _ _
  have hpush : proEtaleRingModuleDirectImage j R S c = sfCompletedModuleDirectImage l E j := by
    unfold proEtaleRingModuleDirectImage sfCompletedModuleDirectImage
    rw [hc]
  let e := (sfOrdinaryModuleAdjunction l E j).leftAdjointUniq
    ((proEtaleRingModuleAdjunction j R S c).ofNatIsoRight (eqToIso hpush))
  let ed := Functor.mapDerivedCategoryNatIso e
  let i := j.opensRange.closedComplement
  have hcomp : Set.range j = (Set.range i)ᶜ := by
    simp only [i, Scheme.Opens.range_closedComplement, compl_compl]
    rfl
  obtain ⟨C⟩ := sfIntegralOrdinaryRecollement_realization l E D.k primeUnit
    (X ↘ Spec (.of D.k)) i j hcomp
  let := sfIntegralConstructible_isClosedUnderIsomorphisms l E U
  intro K
  exact ObjectProperty.prop_of_iso _ (ed.app K.obj) (C.opened.pull_constructible K.obj K.property).1


private theorem openSystemReduction_isIso (D : FiniteFieldDatum.{u})
    (primeUnit : IsUnit (l : D.k)) {U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (K : sfIntegralConstructibleCategory l E U) :
    IsIso ((FrobeniusExchange.compactOperationReduction l E D.k primeUnit j
      (Compactification.ofIsOpenImmersion j)).app K ≫
      (systemDirectId l E X).hom.app
        ((FrobeniusExchange.systemDerivedOpen l E j).obj
          ((FrobeniusExchange.reduction l E U).obj K.obj))) := by
  let c := Compactification.ofIsOpenImmersion j
  let H := FrobeniusExchange.systemDerivedOpen l E j ⋙
    FrobeniusExchange.systemDirect l E (𝟙 X)
  have hi : IsIso ((FrobeniusExchange.operationReduction l E H).app K.obj) := by
    apply (((FrobeniusExchange.models l E).system X).isIso_iff_evaluations _).2
    intro n
    have h := (FrobeniusExchange.compactRealization_existsUnique
      l E D.k primeUnit j c).exists.choose_spec K n
    have hred : IsIso
        ((scalarReductionDerivedExtension l E X n).map
            ((FrobeniusExchange.compactRealization l E D.k primeUnit j c).hom.app K) ≫
          (((FrobeniusExchange.models l E).system X).reductionEvaluation n).inv.app
            ((FrobeniusExchange.compactImage l E j c).obj K.obj) ≫
          (coefficientSequenceDerivedEvaluation l E X n).map
            ((FrobeniusExchange.operationReduction l E H).app K.obj) ≫
          (FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj) :=
      h.symm ▸ (inferInstance :
        IsIso (sfCompactSupportFiniteReductionIso l D.k primeUnit c E K n).hom)
    have hred' : IsIso
        ((((FrobeniusExchange.models l E).system X).reductionEvaluation n).inv.app
            ((FrobeniusExchange.compactImage l E j c).obj K.obj) ≫
          (coefficientSequenceDerivedEvaluation l E X n).map
            ((FrobeniusExchange.operationReduction l E H).app K.obj) ≫
          (FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj) :=
      IsIso.of_isIso_comp_left
        ((scalarReductionDerivedExtension l E X n).map
          ((FrobeniusExchange.compactRealization l E D.k primeUnit j c).hom.app K)) _
    have hred'' : IsIso
        ((coefficientSequenceDerivedEvaluation l E X n).map
            ((FrobeniusExchange.operationReduction l E H).app K.obj) ≫
          (FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj) :=
      IsIso.of_isIso_comp_left
        ((((FrobeniusExchange.models l E).system X).reductionEvaluation n).inv.app
          ((FrobeniusExchange.compactImage l E j c).obj K.obj)) _
    exact IsIso.of_isIso_comp_right _
      ((FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj)
  change IsIso (((FrobeniusExchange.reduction l E X).map
    ((FrobeniusExchange.compactRealization l E D.k primeUnit j c).hom.app K) ≫
    (FrobeniusExchange.operationReduction l E H).app K.obj) ≫ _)
  infer_instance

/-- The ordinary open Hom transpose agrees with the actual whole-system transpose.
This asserts only the pullback presentation and the Hom comparison. It does not
assert preservation of completeness or intervals, finite reduction, shifts, or exactness.

Source: latest blueprint, prop-sf-open-closed-triangle-all-stages.proof.md,
Hom vanishing paragraph and the open adjunction used for its triangle;
Stacks 03DI, 0941 and 0GL1.
(blueprint: lem-sf-open-support-adjunction-transpose).

Proof:
1. Identify the ordinary coefficient pullback with the module pullback of the
   completed ring-sheaf operations by uniqueness of left adjoints. The existing
   ordinary recollement realization then shows it preserves constructibility.
2. Reconstruction units make coherent reduction fully faithful on constructible
   objects. The effective pullback counit is invertible. The prescribed compact
   realization equation and finite-evaluation isomorphism detection make the
   compact-operation comparison invertible as well; remove the identity factor.
   Here evaluation detects only invertibility, never equality of morphisms.
3. Restrict the whole-system open adjunction along coherent reduction using these
   two comparisons. Restrict the ordinary open adjunction using d and its lifted
   ordinary pullback. Uniqueness of right adjoints supplies p so that these two
   restricted adjunctions agree, as checked on their units.
4. Apply the restriction Hom formula, the inverse system Hom equivalence, and
   cancellation of the compact-operation comparison. This proves the displayed
   equality before evaluation. The same adjunction identities include identity
   and empty opens and zero objects. -/
theorem openAdjunctionTransposeNormalization (D : FiniteFieldDatum.{u})
    (primeUnit : IsUnit (l : D.k))
    {U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] :
    let d := (sfQcqsCompactSupportRealization l E D.k primeUnit
      (Compactification.ofIsOpenImmersion j)).symm ≪≫
        isoWhiskerLeft (sfIntegralConstructible l E U).ι (openIdentity l E j)
    ∃ p : constructibleIntegralPullback l E j ⋙ (sfIntegralConstructible l E U).ι ≅
        (sfIntegralConstructible l E X).ι ⋙ ordinaryOpenPull l E j,
      let a := (ordinaryOpenAdjunction l E j).restrictFullyFaithful
        (sfIntegralConstructible l E U).fullyFaithfulι
        (sfIntegralConstructible l E X).fullyFaithfulι d.symm p.symm
      ∀ (N : sfIntegralConstructibleCategory l E U)
        (K : sfIntegralConstructibleCategory l E X)
        (f : (sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
          (Compactification.ofIsOpenImmersion j) E).obj N ⟶ K),
        (FrobeniusExchange.reduction l E X).map f.hom =
          ((FrobeniusExchange.compactOperationReduction l E D.k primeUnit j
            (Compactification.ofIsOpenImmersion j)).app N ≫
            (systemDirectId l E X).hom.app
              ((FrobeniusExchange.systemDerivedOpen l E j).obj
                ((FrobeniusExchange.reduction l E U).obj N.obj))) ≫
          ((FrobeniusExchange.systemDerivedOpenAdjunction l E j).homEquiv _ _).symm
            ((FrobeniusExchange.reduction l E U).map ((a.homEquiv N K) f).hom ≫
              (integralComparisonPullbackCounit l E j
                ((FrobeniusExchange.models l E).system X)
                ((FrobeniusExchange.models l E).system U)
                ((FrobeniusExchange.models l E).roos U)
                ((FrobeniusExchange.models l E).pullback j)).app K.obj) := by
  let L := sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
    (Compactification.ofIsOpenImmersion j) E
  let R := constructibleIntegralPullback l E j
  let iU := (sfIntegralConstructible l E U).ι
  let iX := (sfIntegralConstructible l E X).ι
  let RU := iU ⋙ FrobeniusExchange.reduction l E U
  let RX := iX ⋙ FrobeniusExchange.reduction l E X
  let d := (sfQcqsCompactSupportRealization l E D.k primeUnit
    (Compactification.ofIsOpenImmersion j)).symm ≪≫
      isoWhiskerLeft iU (openIdentity l E j)
  let α : L ⋙ RX ⟶ RU ⋙ FrobeniusExchange.systemDerivedOpen l E j :=
    FrobeniusExchange.compactOperationReduction l E D.k primeUnit j
      (Compactification.ofIsOpenImmersion j) ≫
        whiskerLeft (iU ⋙ FrobeniusExchange.reduction l E U ⋙
          FrobeniusExchange.systemDerivedOpen l E j) (systemDirectId l E X).hom
  let β : R ⋙ RU ⟶ RX ⋙ integralComparisonDerivedSequencePullback l E j :=
    whiskerLeft iX (integralComparisonPullbackCounit l E j
      ((FrobeniusExchange.models l E).system X)
      ((FrobeniusExchange.models l E).system U)
      ((FrobeniusExchange.models l E).roos U)
      ((FrobeniusExchange.models l E).pullback j))
  let : ∀ N, IsIso (α.app N) := fun N ↦ openSystemReduction_isIso l E D primeUnit j N
  let : IsIso α := NatIso.isIso_of_isIso_app α
  let : ∀ K, IsIso (β.app K) := fun K ↦ (FrobeniusExchange.models l E).effective j K
  let : IsIso β := NatIso.isIso_of_isIso_app β
  let fU : RU.FullyFaithful := reductionFullyFaithful _
    ((FrobeniusExchange.models l E).system U).adjunction
    ((FrobeniusExchange.models l E).complete U)
  let fX : RX.FullyFaithful := reductionFullyFaithful _
    ((FrobeniusExchange.models l E).system X).adjunction
    ((FrobeniusExchange.models l E).complete X)
  let a := (FrobeniusExchange.systemDerivedOpenAdjunction l E j).restrictFullyFaithful
    fU fX (asIso α).symm (asIso β).symm
  let R₀ := (sfIntegralConstructible l E U).lift (iX ⋙ ordinaryOpenPull l E j)
    (ordinaryOpenPull_constructible l E D primeUnit j)
  obtain ⟨p, hp⟩ := normalizeRestriction
    (sfIntegralConstructible l E U).fullyFaithfulι
    (sfIntegralConstructible l E X).fullyFaithfulι a (ordinaryOpenAdjunction l E j)
    d (Iso.refl (R₀ ⋙ iU))
  refine ⟨p, ?_⟩
  dsimp only
  rw [hp]
  intro N K f
  have h :=
    (FrobeniusExchange.systemDerivedOpenAdjunction l E j).restrictFullyFaithful_homEquiv_apply
    fU fX (asIso α).symm (asIso β).symm f
  have ht : RU.map ((a.homEquiv N K) f) ≫ β.app K =
      ((FrobeniusExchange.systemDerivedOpenAdjunction l E j).homEquiv _ _)
        (inv (α.app N) ≫ RX.map f) := by
    rw [h, fU.map_preimage]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
      Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app, IsIso.inv_hom_id,
      Category.comp_id]
  have ht' := congrArg
    ((FrobeniusExchange.systemDerivedOpenAdjunction l E j).homEquiv _ _).symm ht
  rw [Equiv.symm_apply_apply] at ht'
  change RX.map f = α.app N ≫
    ((FrobeniusExchange.systemDerivedOpenAdjunction l E j).homEquiv _ _).symm
      (RU.map ((a.homEquiv N K) f) ≫ β.app K)
  rw [ht']
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

end WeilConjectures.IntegralSupportNormalization
