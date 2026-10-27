/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.RealizationCompletedPull
public import Sheaf.Paper.RealizationLocalizedPush
public import Sheaf.Paper.PbcRationalTransport
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.RealizationScalarFunctor
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Mathlib.CategoryTheory.Localization.Adjunction
import Sheaf.Paper.RealizationRestrictionNormalizations
import Sheaf.CategoryTheory.ScalarNormalizedAdjunctionSquare
import all Sheaf.Paper.RealizationPullRationalDescent
import Sheaf.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso

/-! # The specified realization comparisons respect adjunctions

Source: Bhatt--Scholze, Remark 6.8.15, and the scalar-unit calculation in the DAG.
(blueprint: lem-weil-pbc-realization-adjoint-comparisons)

The integral adjunction is characterized by its ambient Hom transpose, using
precisely the strict completion unit. The rational assertion retains tensor units
and counits, and the same integral comparison components.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u uC uD uC' uD' vC vD vC' vD'
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable {l : ℕ} [Fact l.Prime] {E : Type u} [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {k : Type u} [Field k] {T U : RealizationPullScheme l k}
  {h : T.scheme ⟶ U.scheme}
  {sT : RealizationScalarFunctorData l E T.scheme}
  {sU : RealizationScalarFunctorData l E U.scheme}

/-- Restrict the specified ordinary integral direct image, without completing it.
Source: BS Remark 6.8.15
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def RealizationLocalizedPushData.integralPush
    (b : RealizationLocalizedPushData l E h sT sU) :=
  pbcConditionalIntegral (pbcIntegralDatum l E)
    (proEtaleRingDerivedDirectImage h _ _ b.integralPullback) b.integral

/-- The ambient continuous-coefficient adjunction, in the published section coordinates.
Source: BS Remark 6.8.15
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def realizationContinuousAdjunction
    (a : RealizationCompletedPullArrow T U h sT sU) :=
  proEtaleRingDerivedAdjunction h (rationalCoefficientSheaf l U.scheme E)
    (rationalCoefficientSheaf l T.scheme E) a.rationalCoefficient

/-- The same specified alpha, with only the scalar-map abbreviation unfolded.
Source: BS Remark 6.8.15
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def realizationAdjointAlpha
    (a : RealizationCompletedPullArrow T U h sT sU) :
    a.integralCompleted ⋙
        (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
          pbcDerivedExtend (sT.scalarMap l E T.scheme)) ≅
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (sU.scalarMap l E U.scheme)) ⋙ a.continuousPull := by
  simpa only [RealizationScalarFunctorData.scalarMap,
    RealizationCompletedPullArrow.integralCompleted, pbcConditionalIntegral,
    RealizationCompletedPullArrow.continuousPull, realizationPullScalarMap,
    Functor.assoc] using
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (ObjectProperty.liftCompιIso _ _ a.completed_mem) _ ≪≫ a.alpha)

/-- The published integral realization comparison in the common scalar coordinates.
Source: BS Remark 6.8.15
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def realizationAdjointIntegral {V : Scheme.{u}} [IsNoetherian V]
    [Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
    [Fact (∀ t : V, IsUnit (l : V.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E V) :
    pbcRationalization V (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        realizationPullRationalScalar l E s ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete V (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (s.scalarMap l E V) := by
  simpa only [realizationPullScalarMap, RealizationScalarFunctorData.scalarMap] using
    realizationPullIntegral l E s

/-- Tensor extension of the actual integral direct image.
Source: BS Remark 6.8.15; rational transport, blueprint order 1306
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def realizationRationalPush (b : RealizationLocalizedPushData l E h sT sU)
    (qAdd : b.integralPush.Additive) (qLin : b.integralPush.Linear (PbcIntegralRing l E)) :=
  letI := qAdd
  letI := qLin
  ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) b.integralPush

/-- Compatibility with the two adjunctions, expressed by the node's two equations.
Source: BS Remark 6.8.15
(blueprint: lem-weil-pbc-realization-adjoint-comparisons). -/
def RealizationAdjointEquations
    {C : Type uC} {D : Type uD} {C' : Type uC'} {D' : Type uD'}
    [Category.{vC} C] [Category.{vD} D] [Category.{vC'} C'] [Category.{vD'} D']
    {P : C ⥤ D} {Q : D ⥤ C} {PE : C' ⥤ D'} {QE : D' ⥤ C'}
    (adj : P ⊣ Q) (adjE : PE ⊣ QE) (FU : C ⥤ C') (FT : D ⥤ D')
    (alpha : P ⋙ FT ⟶ FU ⋙ PE) (beta : Q ⋙ FU ⟶ FT ⋙ QE) : Prop :=
  (∀ N : C, FU.map (adj.unit.app N) ≫ beta.app (P.obj N) ≫ QE.map (alpha.app N) =
    adjE.unit.app (FU.obj N)) ∧
  (∀ M : D, FT.map (adj.counit.app M) =
    alpha.app (Q.obj M) ≫ PE.map (beta.app M) ≫ adjE.counit.app (FT.obj M))

section RationalSquare
universe r
variable (R : Type r) [CommRing R] (t : R)
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [Linear R D]
  (WC : MorphismProperty C) (WD : MorphismProperty D)
  [(ScalarLocalization.localization R C t).IsLocalization WC]
  [(ScalarLocalization.localization R D t).IsLocalization WD]
  (P : C ⥤ D) (Q : D ⥤ C) [P.Additive] [P.Linear R] [Q.Additive] [Q.Linear R]

private def tensorAdjunction (adj : P ⊣ Q) :
    ScalarLocalization.transport R t P ⊣ ScalarLocalization.transport R t Q := by
  let : CatCommSq P (ScalarLocalization.localization R C t)
      (ScalarLocalization.localization R D t) (ScalarLocalization.transport R t P) :=
    ⟨(transportIntegral R t P).symm⟩
  let : CatCommSq Q (ScalarLocalization.localization R D t)
      (ScalarLocalization.localization R C t) (ScalarLocalization.transport R t Q) :=
    ⟨(transportIntegral R t Q).symm⟩
  exact adj.localization (ScalarLocalization.localization R C t) WC
    (ScalarLocalization.localization R D t) WD _ _

private theorem tensorAdjunction_unit (adj : P ⊣ Q) (N : C) :
    (tensorAdjunction R t WC WD P Q adj).unit.app ⟨N⟩ =
      (ScalarLocalization.localization R C t).map (adj.unit.app N) := by
  dsimp only [tensorAdjunction]
  erw [Adjunction.localization_unit_app]
  simp only [CatCommSq.iso, transportIntegral, Iso.symm_hom, NatIso.ofComponents_inv_app]
  change (ScalarLocalization.localization R C t).map (adj.unit.app N) ≫
    𝟙 _ ≫ (ScalarLocalization.transport R t Q).map (𝟙 (⟨P.obj N⟩ : ScalarLocalization R D t)) = _
  rw [(ScalarLocalization.transport R t Q).map_id]
  dsimp only [ScalarLocalization.transport, ScalarLocalization.localization, Functor.comp_obj]
  simp only [Category.comp_id]

private theorem tensorAdjunction_counit (adj : P ⊣ Q) (M : D) :
    (tensorAdjunction R t WC WD P Q adj).counit.app ⟨M⟩ =
      (ScalarLocalization.localization R D t).map (adj.counit.app M) := by
  dsimp only [tensorAdjunction]
  erw [Adjunction.localization_counit_app]
  simp only [CatCommSq.iso, transportIntegral, Iso.symm_inv, NatIso.ofComponents_hom_app]
  change (ScalarLocalization.transport R t P).map (𝟙 (⟨Q.obj M⟩ : ScalarLocalization R C t)) ≫ 𝟙 _ ≫
    (ScalarLocalization.localization R D t).map (adj.counit.app M) = _
  rw [(ScalarLocalization.transport R t P).map_id, Category.id_comp, Category.id_comp]

end RationalSquare

private theorem descendIso
    {C : Type uC} {D : Type uD} {B : Type uC'}
    [Category.{vC} C] [Category.{vD} D] [Category.{vC'} B]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F G : D ⥤ B} (i : L ⋙ F ≅ L ⋙ G) :
    ∃ e : F ≅ G, ∀ N : C, e.hom.app (L.obj N) = i.hom.app N := by
  let H := (Functor.whiskeringLeft C D B).obj L
  have : H.Full := Localization.full_whiskeringLeft L W B
  have : H.Faithful := Localization.faithful_whiskeringLeft L W B
  refine ⟨H.preimageIso i, fun N ↦ ?_⟩
  exact NatTrans.congr_app (H.map_preimage i.hom) N

private theorem rationalAdjointSquare
    (R : Type*) [CommRing R] (t : R)
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [Linear R D]
    (WC : MorphismProperty C) (WD : MorphismProperty D)
    [(ScalarLocalization.localization R C t).IsLocalization WC]
    [(ScalarLocalization.localization R D t).IsLocalization WD]
    (P : C ⥤ D) (Q : D ⥤ C) [P.Additive] [P.Linear R] [Q.Additive] [Q.Linear R]
    (adj : P ⊣ Q)
    {C' : Type uC'} {D' : Type uD'} [Category.{vC'} C'] [Category.{vD'} D']
    (PE : C' ⥤ D') (QE : D' ⥤ C') (adjE : PE ⊣ QE)
    (FU : C ⥤ C') (FT : D ⥤ D')
    (FUr : ScalarLocalization R C t ⥤ C') (FTr : ScalarLocalization R D t ⥤ D')
    (IU : ScalarLocalization.localization R C t ⋙ FUr ≅ FU)
    (IT : ScalarLocalization.localization R D t ⋙ FTr ≅ FT)
    (α : P ⋙ FT ≅ FU ⋙ PE) (β : Q ⋙ FU ≅ FT ⋙ QE)
    (eqI : RealizationAdjointEquations adj adjE FU FT α.hom β.hom) :
    ∃ adjR : ScalarLocalization.transport R t P ⊣ ScalarLocalization.transport R t Q,
      (∀ N : C, adjR.unit.app ⟨N⟩ =
        (ScalarLocalization.localization R C t).map (adj.unit.app N)) ∧
      (∀ M : D, adjR.counit.app ⟨M⟩ =
        (ScalarLocalization.localization R D t).map (adj.counit.app M)) ∧
      ∃ (αR : ScalarLocalization.transport R t P ⋙ FTr ≅ FUr ⋙ PE)
        (βR : ScalarLocalization.transport R t Q ⋙ FUr ≅ FTr ⋙ QE),
        (∀ N : C, αR.hom.app ⟨N⟩ =
          IT.hom.app (P.obj N) ≫ α.hom.app N ≫ PE.map (IU.inv.app N)) ∧
        (∀ M : D, βR.hom.app ⟨M⟩ =
          IU.hom.app (Q.obj M) ≫ β.hom.app M ≫ QE.map (IT.inv.app M)) ∧
        RealizationAdjointEquations adjR adjE FUr FTr αR.hom βR.hom := by
  let LC := ScalarLocalization.localization R C t
  let LD := ScalarLocalization.localization R D t
  let Pr := ScalarLocalization.transport R t P
  let Qr := ScalarLocalization.transport R t Q
  let adjR := tensorAdjunction R t WC WD P Q adj
  let αI : LC ⋙ (Pr ⋙ FTr) ≅ LC ⋙ (FUr ⋙ PE) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (transportIntegral R t P) FTr ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft P IT ≪≫ α ≪≫
      Functor.isoWhiskerRight IU.symm PE ≪≫ Functor.associator _ _ _
  let βI : LD ⋙ (Qr ⋙ FUr) ≅ LD ⋙ (FTr ⋙ QE) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (transportIntegral R t Q) FUr ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Q IU ≪≫ β ≪≫
      Functor.isoWhiskerRight IT.symm QE ≪≫ Functor.associator _ _ _
  obtain ⟨αR, hα⟩ := descendIso LC WC αI
  obtain ⟨βR, hβ⟩ := descendIso LD WD βI
  have hαR (N : C) : αR.hom.app ⟨N⟩ =
      IT.hom.app (P.obj N) ≫ α.hom.app N ≫ PE.map (IU.inv.app N) := by
    erw [hα]
    simp only [αI, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id]
    change FTr.map (𝟙 _) ≫ _ = _
    erw [FTr.map_id, Category.id_comp]
  have hβR (M : D) : βR.hom.app ⟨M⟩ =
      IU.hom.app (Q.obj M) ≫ β.hom.app M ≫ QE.map (IT.inv.app M) := by
    erw [hβ]
    simp only [βI, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id]
    change FUr.map (𝟙 _) ≫ _ = _
    erw [FUr.map_id, Category.id_comp]
  have hu := tensorAdjunction_unit R t WC WD P Q adj
  have he := tensorAdjunction_counit R t WC WD P Q adj
  refine ⟨adjR, hu, he, αR, βR, hαR, hβR, ?_⟩
  constructor
  · intro N
    change FUr.map (adjR.unit.app ⟨N.obj⟩) ≫ βR.hom.app ⟨P.obj N.obj⟩ ≫
      QE.map (αR.hom.app ⟨N.obj⟩) = _
    erw [hu, hβR, hαR, QE.map_comp, QE.map_comp]
    simp only [Category.assoc]
    erw [← QE.map_comp_assoc (IT.inv.app _) (IT.hom.app _),
      IT.inv_hom_id_app, QE.map_id, Category.id_comp]
    have hn := IU.hom.naturality (adj.unit.app N.obj)
    change FUr.map (LC.map (adj.unit.app N.obj)) ≫ IU.hom.app (Q.obj (P.obj N.obj)) =
      IU.hom.app N.obj ≫ FU.map (adj.unit.app N.obj) at hn
    erw [reassoc_of% hn]
    calc
      _ = IU.hom.app N.obj ≫ adjE.unit.app (FU.obj N.obj) ≫
          QE.map (PE.map (IU.inv.app N.obj)) := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ IU.hom.app N.obj ≫ z ≫ QE.map (PE.map (IU.inv.app N.obj)))
          (eqI.1 N.obj)
      _ = _ := by
        erw [← Category.assoc, adjE.unit.naturality (IU.hom.app N.obj)]
        simp only [Functor.comp_map, Category.assoc,
          ← QE.map_comp, ← PE.map_comp, IU.hom_inv_id_app, PE.map_id, QE.map_id]
        change adjE.unit.app (FUr.obj N) ≫ 𝟙 _ = _
        exact Category.comp_id _
  · intro M
    change FTr.map (adjR.counit.app ⟨M.obj⟩) =
      αR.hom.app ⟨Q.obj M.obj⟩ ≫ PE.map (βR.hom.app ⟨M.obj⟩) ≫ _
    apply (cancel_mono (IT.hom.app M.obj)).1
    erw [he, hαR, hβR]
    have hn := IT.hom.naturality (adj.counit.app M.obj)
    change FTr.map (LD.map (adj.counit.app M.obj)) ≫ IT.hom.app M.obj =
      IT.hom.app (P.obj (Q.obj M.obj)) ≫ FT.map (adj.counit.app M.obj) at hn
    erw [hn, eqI.2]
    have hc := adjE.counit.naturality (IT.hom.app M.obj)
    change PE.map (QE.map (IT.hom.app M.obj)) ≫ adjE.counit.app (FT.obj M.obj) =
      adjE.counit.app (FTr.obj M) ≫ IT.hom.app M.obj at hc
    simp only [Category.assoc]
    erw [← hc]
    simp only [PE.map_comp, Category.assoc]
    erw [← PE.map_comp_assoc (IU.inv.app _) (IU.hom.app _),
      IU.inv_hom_id_app, PE.map_id, Category.id_comp]
    erw [← PE.map_comp_assoc (QE.map (IT.inv.app _)) (QE.map (IT.hom.app _)),
      ← QE.map_comp, IT.inv_hom_id_app, QE.map_id, PE.map_id, Category.id_comp]

private theorem pushCoefficient_eq
    (a : RealizationCompletedPullArrow T U h sT sU)
    (b : RealizationLocalizedPushData l E h sT sU) :
    b.integralPullback = realizationRestrictionCoefficient a := by
  apply Iso.ext
  exact b.integralPullback_normalization

private theorem rationalCoefficient_eq
    (a : RealizationCompletedPullArrow T U h sT sU)
    (b : RealizationLocalizedPushData l E h sT sU) :
    b.rationalPullback = a.rationalCoefficient := by
  apply Iso.ext
  apply ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _).injective
  apply Sheaf.hom_ext
  ext V s
  apply rationalCoefficientValue_ext l E T.scheme ((proEtaleBaseChange h).op.obj V)
  intro x
  exact (rationalCoefficientDirectImage_value l E h b.rationalPullback.hom
    b.rationalPullback_normalization V.unop s x).trans
    (rationalCoefficientDirectImage_value l E h a.rationalCoefficient.hom
      a.rational_normalization V.unop s x).symm

unseal realizationPullScalarMap in
/-- The specified beta is the mate of alpha inverse, integrally and after raw
scalar localization. No properness, rational lattice, or idempotent completion is used.
Source: Bhatt--Scholze, Remark 6.8.15; the DAG scalar-adjunction calculation.
(blueprint: lem-weil-pbc-realization-adjoint-comparisons)

Proof:
1. Remove the invertible strict completion units using completed-pull. Ordinary
pullback and direct image preserve the integral full subcategories. Restoring the
units at the end transports precisely the characterized integral adjunction.
2. The finite coefficient normalizations identify the maps with precomposition.
The coefficient square commutes with A to E; localization preserves its numerator
and denominator. Ring-sheaf change adjunction supplies ambient comparisons b and d
for restriction of scalars and pullback and direct image, with compatible adjuncts.
3. The specified comparisons obey r(alpha) j = b inverse P(j) and
r(beta) j = d inverse Q(j), by their localization-unit normalizations.
4. Apply the coefficient-change adjunct equation to the continuous counit, whose
adjunct is identity. Its restricted adjunct is d, so r(epsilonE) b inverse = epsilon P(d).
5. Transpose the proposed counit equation under scalar extension/restriction.
Use step 3, naturality of b, step 3 again, and step 4. Both sides become j epsilon,
by naturality of the ambient integral counit. Injectivity proves the counit equation,
equivalently that beta is the mate of alpha inverse.
6. Transpose the unit composite under the continuous adjunction. Naturality of
its counit, step 5 at PN, naturality of alpha, and the integral triangle identity
make its transpose identity. The continuous unit has the same transpose. Injectivity
proves the unit equation; restore the completion units as in step 1.
7. Extend the actual linear functors and transformations by rational transport.
On a fraction naturality is the integral equality times the inverse denominator.
The tensor units and counits satisfy the triangles componentwise. Every raw object
is integral, and the extended alpha and beta have the displayed integral components,
conjugated by the scalar functor's integral comparison. The two equations therefore
persist for every raw object. -/
theorem realization_adjoint_comparisons
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (T U : RealizationPullScheme l k) (h : T.scheme ⟶ U.scheme)
    [h.IsOver (Spec (.of k))]
    (sT : RealizationScalarFunctorData l E T.scheme)
    (sU : RealizationScalarFunctorData l E U.scheme)
    (a : RealizationCompletedPullArrow T U h sT sU)
    (b : RealizationLocalizedPushData l E h sT sU) :
    ∃ rationalCoefficients : b.rationalPullback = a.rationalCoefficient,
    ∃ adj : a.integralCompleted ⊣ b.integralPush,
    (∀ (N : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E))
      (M : PbcBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E))
      (f : a.integralCompleted.obj N ⟶ M),
      HEq ((adj.homEquiv N M f).hom)
        ((pbcActualDerivedAdjunction h (pbcIntegralDatum l E)).homEquiv N.obj M.obj
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app N.obj ≫ f.hom))) ∧
    RealizationAdjointEquations adj
      (realizationContinuousAdjunction a)
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (sU.scalarMap l E U.scheme))
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (sT.scalarMap l E T.scheme))
      (realizationAdjointAlpha a).hom
      (b.beta ≫ eqToHom (congrArg (fun c ↦
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
          pbcDerivedExtend (sT.scalarMap l E T.scheme) ⋙
            proEtaleRingDerivedDirectImage h _ _ c) rationalCoefficients)) ∧
    ∃ (qAdd : b.integralPush.Additive) (qLin : b.integralPush.Linear (PbcIntegralRing l E))
      (adjR : a.rationalCompleted ⊣ realizationRationalPush b qAdd qLin),
      (∀ N : PbcRationalCategory U.scheme (pbcIntegralDatum l E) (pbcUniformizer l E),
        adjR.unit.app N =
        (pbcRationalization U.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
          (adj.unit.app N.obj)) ∧
      (∀ M : PbcRationalCategory T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E),
        adjR.counit.app M =
        (pbcRationalization T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
          (adj.counit.app M.obj)) ∧
      ∃ (alphaR : a.rationalCompleted ⋙ realizationPullRationalScalar l E sT ≅
          realizationPullRationalScalar l E sU ⋙ a.continuousPull)
        (betaR : realizationRationalPush b qAdd qLin ⋙ realizationPullRationalScalar l E sU ≅
          realizationPullRationalScalar l E sT ⋙
            proEtaleRingDerivedDirectImage h _ _ a.rationalCoefficient),
        (∀ N : PbcBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E),
          alphaR.hom.app ⟨N⟩ =
          (realizationAdjointIntegral sT).hom.app (a.integralCompleted.obj N) ≫
            (realizationAdjointAlpha a).hom.app N ≫
            a.continuousPull.map ((realizationAdjointIntegral sU).inv.app N)) ∧
        (∀ M : PbcBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E),
          betaR.hom.app ⟨M⟩ ≫
            (proEtaleRingDerivedDirectImage h _ _ a.rationalCoefficient).map
              ((realizationAdjointIntegral sT).hom.app M) =
          (realizationAdjointIntegral sU).hom.app (b.integralPush.obj M) ≫
            b.beta.app M ≫
            (eqToHom (congrArg (fun c ↦ proEtaleRingDerivedDirectImage h _ _ c)
              rationalCoefficients)).app ((pbcDerivedExtend (sT.scalarMap l E T.scheme)).obj
                M.obj)) ∧
        RealizationAdjointEquations adjR (realizationContinuousAdjunction a)
          (realizationPullRationalScalar l E sU) (realizationPullRationalScalar l E sT)
          alphaR.hom betaR.hom := by
  classical
  have hA := pushCoefficient_eq a b
  have hE := rationalCoefficient_eq a b
  rcases b with ⟨cA, hcA, cE, hcE, sq, cont, mem, comp, β, βiso, βnorm⟩
  dsimp only at hA hE
  subst cA
  subst cE
  let CU : ObjectProperty (PbcCompletedDerived U.scheme (pbcIntegralDatum l E)) :=
    PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)
  let DT : ObjectProperty (PbcCompletedDerived T.scheme (pbcIntegralDatum l E)) :=
    PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)
  let FU := CU.ι ⋙ pbcDerivedExtend (sU.scalarMap l E U.scheme)
  let FT := DT.ι ⋙ pbcDerivedExtend (sT.scalarMap l E T.scheme)
  let Q := pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualDerivedPush h (pbcIntegralDatum l E)) mem
  let adjA := pbcActualDerivedAdjunction h (pbcIntegralDatum l E)
  let adjO : a.integralOrdinary ⊣ Q := adjA.restrictFullyFaithful
    CU.fullyFaithfulι DT.fullyFaithfulι (Iso.refl _) (Iso.refl _)
  let γ : a.integralOrdinary ≅ a.integralCompleted :=
    NatIso.ofComponents (fun N ↦ by
      let := a.unit_isIso N
      exact ObjectProperty.isoMk _
        (asIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app N.obj)))
      (by
        intro N M f
        apply ObjectProperty.hom_ext
        exact (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).naturality f.hom)
  let adj := adjO.ofNatIsoLeft γ
  let αc := realizationAdjointAlpha a
  let αo : CU.ι ⋙ pbcActualDerivedPull h (pbcIntegralDatum l E) ⋙
        pbcDerivedExtend (sT.scalarMap l E T.scheme) ≅
      CU.ι ⋙ pbcDerivedExtend (sU.scalarMap l E U.scheme) ⋙ a.continuousPull :=
    Functor.isoWhiskerRight γ FT ≪≫ αc
  obtain ⟨p, hpA, hpE, hnα, hnβ, hnε⟩ := realization_restriction_normalizations a
  have hα := hnα
  have hε := hnε
  have hb (M : DT.FullSubcategory) :
      (pbcDerivedScalarAdjunction (sU.scalarMap l E U.scheme)).unit.app
          ((pbcActualDerivedPush h (pbcIntegralDatum l E)).obj M.obj) ≫
        (pbcDerivedRestrict (sU.scalarMap l E U.scheme)).map (β.app M) =
      (pbcActualDerivedPush h (pbcIntegralDatum l E)).map
          ((pbcDerivedScalarAdjunction (sT.scalarMap l E T.scheme)).unit.app M.obj) ≫
        (realizationRestrictionPush a).inv.app
          ((pbcDerivedExtend (sT.scalarMap l E T.scheme)).obj M.obj) := by
    exact βnorm M
  have hs := Adjunction.scalarNormalizedAdjunctionSquare adjA
    (realizationContinuousAdjunction a)
    (pbcDerivedScalarAdjunction (sU.scalarMap l E U.scheme))
    (pbcDerivedScalarAdjunction (sT.scalarMap l E T.scheme))
    CU DT a.ordinary_mem mem
    (realizationRestrictionPull a) (realizationRestrictionPush a) αo β
    (fun N ↦ by
      have ha : αo.hom.app N = realizationRestrictionAlpha a N := by
        change (pbcDerivedExtend (sT.scalarMap l E T.scheme)).map
            ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app N.obj) ≫
          (𝟙 _ ≫ (pbcDerivedExtend (sT.scalarMap l E T.scheme)).map (𝟙 _) ≫
            a.alpha.hom.app N) = _
        erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
        rfl
      rw [ha]
      simpa only [realizationPullScalarMap, RealizationScalarFunctorData.scalarMap] using hα N)
    hb (by
      simpa only [realizationPullScalarMap, RealizationScalarFunctorData.scalarMap,
        realizationContinuousAdjunction, adjA] using hε)
  clear hα hε hb hnα hnβ hnε hpA hpE p
  have huO (N : CU.FullSubcategory) :
      FU.map (adjO.unit.app N) ≫ β.app (a.integralOrdinary.obj N) ≫
        (proEtaleRingDerivedDirectImage h _ _ a.rationalCoefficient).map (αo.hom.app N) =
      (realizationContinuousAdjunction a).unit.app (FU.obj N) := by
    have he := adjA.map_restrictFullyFaithful_unit_app CU.fullyFaithfulι
      DT.fullyFaithfulι (L := a.integralOrdinary) (R := Q) (Iso.refl _) (Iso.refl _) N
    simp only [Iso.refl_hom, NatTrans.id_app] at he
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at he
    change (adjO.unit.app N).hom = adjA.unit.app N.obj at he
    change (pbcDerivedExtend (sU.scalarMap l E U.scheme)).map
      ((adjO.unit.app N).hom) ≫ _ ≫ _ = _
    erw [he]
    exact (hs.2.1 N).2
  have heO (M : DT.FullSubcategory) :
      FT.map (adjO.counit.app M) = αo.hom.app (Q.obj M) ≫
        a.continuousPull.map (β.app M) ≫
          (realizationContinuousAdjunction a).counit.app (FT.obj M) := by
    have he := adjA.map_restrictFullyFaithful_counit_app CU.fullyFaithfulι
      DT.fullyFaithfulι (L := a.integralOrdinary) (R := Q) (Iso.refl _) (Iso.refl _) M
    simp only [Iso.refl_inv, NatTrans.id_app] at he
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at he
    change (adjO.counit.app M).hom = adjA.counit.app M.obj at he
    change (pbcDerivedExtend (sT.scalarMap l E T.scheme)).map
      ((adjO.counit.app M).hom) = _
    erw [he]
    exact (hs.1 M).2.2
  have eqI : RealizationAdjointEquations adj (realizationContinuousAdjunction a)
      FU FT αc.hom β := by
    constructor
    · intro N
      change FU.map (adjO.unit.app N ≫ Q.map (γ.hom.app N)) ≫ _ ≫ _ = _
      rw [FU.map_comp, Category.assoc]
      have hn := β.naturality (γ.hom.app N)
      change FU.map (Q.map (γ.hom.app N)) ≫ β.app (a.integralCompleted.obj N) =
        β.app (a.integralOrdinary.obj N) ≫
          (proEtaleRingDerivedDirectImage h _ _ a.rationalCoefficient).map
            (FT.map (γ.hom.app N)) at hn
      rw [reassoc_of% hn, ← CategoryTheory.Functor.map_comp]
      exact huO N
    · intro M
      change FT.map (γ.inv.app (Q.obj M) ≫ adjO.counit.app M) = _
      rw [FT.map_comp, heO]
      simp only [αo, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, ← Category.assoc, ← FT.map_comp,
        Iso.inv_hom_id_app, FT.map_id, Category.id_comp]
      rfl
  clear hs huO heO
  refine ⟨rfl, adj, ?_, ?_, ?_⟩
  · intro N M f
    apply heq_of_eq
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
    change ((adjO.homEquiv N M (γ.hom.app N ≫ f)).hom) = _
    rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
    simp only [Iso.refl_hom, NatTrans.id_app]
    simp only [Adjunction.homEquiv_apply, CategoryTheory.Functor.map_comp, Category.assoc]
    change adjA.unit.app N.obj ≫
      (pbcActualDerivedPush h (pbcIntegralDatum l E)).map (𝟙 _) ≫
      (pbcActualDerivedPush h (pbcIntegralDatum l E)).map (γ.hom.app N).hom ≫
      (pbcActualDerivedPush h (pbcIntegralDatum l E)).map f.hom ≫ 𝟙 _ = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    rfl
  · simpa only [eqToHom_refl, Category.comp_id] using eqI
  · let qAdd : Q.Additive :=
      (pbcConditionalIntegral_linear (pbcIntegralDatum l E)
        (pbcActualDerivedPush h (pbcIntegralDatum l E)) mem).1
    let qLin : Q.Linear (PbcIntegralRing l E) :=
      (pbcConditionalIntegral_linear (pbcIntegralDatum l E)
        (pbcActualDerivedPush h (pbcIntegralDatum l E)) mem).2
    let : a.integralCompleted.Additive := a.completedAdditive
    let : a.integralCompleted.Linear (PbcIntegralRing l E) := a.completedLinear
    let := integralLocalization (E := E) U
    let := integralLocalization (E := E) T
    let : ∀ M, IsIso (β.app M) := βiso
    have : IsIso β := NatIso.isIso_of_isIso_app β
    let βi : Q ⋙ FU ≅ FT ⋙ proEtaleRingDerivedDirectImage h _ _ a.rationalCoefficient :=
      asIso β
    obtain ⟨adjR, hu, he, αR, βR, hαR, hβR, eqR⟩ := rationalAdjointSquare
      (PbcIntegralRing l E) (pbcUniformizer l E)
      (Rationalization.W (Submonoid.powers (pbcUniformizer l E)) CU.FullSubcategory)
      (Rationalization.W (Submonoid.powers (pbcUniformizer l E)) DT.FullSubcategory)
      a.integralCompleted Q adj a.continuousPull
      (proEtaleRingDerivedDirectImage h _ _ a.rationalCoefficient)
      (realizationContinuousAdjunction a) FU FT
      (realizationPullRationalScalar l E sU) (realizationPullRationalScalar l E sT)
      (realizationAdjointIntegral sU) (realizationAdjointIntegral sT) αc βi eqI
    refine ⟨qAdd, qLin, adjR, (fun N ↦ hu N.obj), (fun M ↦ he M.obj),
      αR, βR, hαR, ?_, eqR⟩
    intro M
    rw [hβR]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, eqToHom_refl, NatTrans.id_app]
    rfl

end WeilConjectures
