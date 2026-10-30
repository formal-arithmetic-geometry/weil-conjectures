/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import all WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeartClosure
import WeilConjectures.AlgebraicGeometry.IntegralConstantModelCriterion
import WeilConjectures.AlgebraicGeometry.IntegralModelsCompletionTransport
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksBasic
import WeilConjectures.SixFunctors.ProEtale.InternalCompletionStacksComparison
import WeilConjectures.SixFunctors.ProEtale.InternalResidueStacksComparison

/-! # Integral models and Stacks adic constructibility

This file proves `det-lem-integral-models-stacks` along the blueprint route: restriction of
scalars along the map from the constant coefficient ring, the integral constructibility
criterion `sk-prop-integral-criterion`, part (2) of
`det-prop-integral-criterion-constant-coefficients` and the pro-étale/étale comparison of
constructible complexes. The criterion is stated in the internal presentation over
`DerivedNakayama.integerRing` (`internal_integral_criterion_forward`,
`internal_integral_criterion_reverse`), where completeness is the Roos condition
`IsDerivedComplete` and the residue is `AdicCompletion.derivedReduction`.

Here `Dᵇc(X, 𝒪_E)` is `constantModelBoundedConstructible`, the finite-constant-model form of
`sk-def-sfb-constructible`. For this form the reverse implication of the criterion needs the
local structure theorem `sk-prop-integral-local-structure`; it is supplied by the adic stratified
perfect models through `constantModelBoundedConstructible_iff_stacksConstructible`.

## Main statements

* `integral_models_stacks_criterion`: `K ∈ Dᵇc(X, 𝒪_E)` iff `Res K` is Stacks adic
  constructible.
* `integral_models_stacks`: in addition, `Res` restricts to an equivalence of the two full
  subcategories.

Source: blueprint det-lem-integral-models-stacks; Stacks Tag 09C1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- Local derived completeness for the first residue map, transported to the small site:
the completeness clause of `stacksConstructible`.
Source: Stacks Tag 09C1 (auxiliary; not a blueprint node). -/
def stacksComplete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X))) :=
  fun L ↦ ConstantCompletion.IsComplete (smallMap X (residueMap l E X))
    (smallDerivedObject X _ L)

/-- The complexes over the continuous integers whose restriction to the constant integers is
complete in the sense of `stacksComplete`.
Source: blueprint det-lem-integral-models-stacks
(auxiliary; not a blueprint node). -/
def restrictionComplete (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :=
  fun K ↦ stacksComplete l E X ((restriction l E X).obj K)

/-- Transport along `IntegralConstantModel.pointComparison` from the internal presentation
over `DerivedNakayama.integerRing` to the continuous integers `integersObj` preserves and
reflects bounded constant-model constructibility.
Source: blueprint det-lem-integral-models-stacks (auxiliary; not a blueprint node).

Proof: restriction of scalars along an isomorphism of coefficient rings is an exact
equivalence, so it preserves and reflects boundedness, commutes with cohomology, and
`constantModel_comap_iff` transports the finite constant models. -/
theorem constantModelBoundedConstructible_pointComparison_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K ↔
      constantModelBoundedConstructible (integersObj l E) X
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
          ).mapDerivedCategory.obj K) := by
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  have hF : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  apply and_congr
  · exact ⟨F.bounded_mapDerivedCategory_obj, F.bounded_of_bounded_mapDerivedCategory_obj⟩
  · apply forall_congr'
    intro q
    have h := constantModel_comap_iff (IntegralConstantModel.pointComparison l E).inv.hom
      X ((DerivedCategory.homologyFunctor _ q).obj K)
    have hi' := (constantModelConstructibleFiniteTor_wellDefined (integersObj l E) X).1
    let := hi'
    exact h.symm.trans
      ⟨fun h ↦ ObjectProperty.prop_of_iso _
        ((F.mapDerivedCategoryHomologyFunctorIso q).app K) h,
      fun h ↦ ObjectProperty.prop_of_iso _
        ((F.mapDerivedCategoryHomologyFunctorIso q).app K).symm h⟩

/-- Integral constructibility criterion, direction (1) to (2), in the internal presentation:
a bounded constructible complex over the continuous integers is derived complete, and its
first derived reduction is bounded constructible of finite Tor amplitude. This is the
implication (1) ⇒ (2) of `sk-prop-integral-criterion` (Bhatt–Scholze, Proposition 6.8.11),
together with finite Tor amplitude of the reduction over the residue field, as used in the
proof of `det-lem-integral-models-stacks`.
Source: Bhatt–Scholze 6.8.11; Stacks Tag 09C7
(blueprint: sk-prop-integral-criterion).

Proof: transport `K` to the continuous integers
(`constantModelBoundedConstructible_pointComparison_iff`),
apply `constantModelBoundedConstructible_iff_stacksConstructible`, and read the two clauses of
`stacksConstructible` back by `internal_completion_stacks_comparison` and
`internal_residue_stacks_comparison`. -/
theorem internal_integral_criterion_forward
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K) :
    IsDerivedComplete l E X K ∧
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
        ((AdicCompletion.derivedReduction l E X 0).obj K) ∧
      _root_.DerivedCategory.finiteTorAmplitude _
        ((AdicCompletion.derivedReduction l E X 0).obj K) := by
  have h := (constantModelBoundedConstructible_iff_stacksConstructible l E X _).mp
    ((constantModelBoundedConstructible_pointComparison_iff l E X K).mp hK)
  exact ⟨(internal_completion_stacks_comparison l E X K).mpr h.1,
    (internal_residue_stacks_comparison l E X K).mp h.2⟩

/-- Integral constructibility criterion, direction (2) to (1), in the internal presentation:
a derived complete complex whose first derived reduction is bounded constructible of finite
Tor amplitude is bounded constructible over the continuous integers. This is the implication
(2) ⇒ (1) of `sk-prop-integral-criterion` (Bhatt–Scholze, Proposition 6.8.11), in the form of
Stacks Tag 09C7 (the reduction lies in `D_ctf`); its proof goes through (3) by
`sk-prop-integral-local-structure`.
Source: Bhatt–Scholze 6.8.11; Stacks Tag 09C7
(blueprint: sk-prop-integral-criterion).

Proof: `internal_completion_stacks_comparison` and `internal_residue_stacks_comparison` show
that the restriction of the transported complex is Stacks adic constructible; conclude by
`constantModelBoundedConstructible_iff_stacksConstructible` and
`constantModelBoundedConstructible_pointComparison_iff`. -/
theorem internal_integral_criterion_reverse
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hc : IsDerivedComplete l E X K)
    (hr : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X
      ((AdicCompletion.derivedReduction l E X 0).obj K))
    (ht : _root_.DerivedCategory.finiteTorAmplitude _
      ((AdicCompletion.derivedReduction l E X 0).obj K)) :
    constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K :=
  (constantModelBoundedConstructible_pointComparison_iff l E X K).mpr
    ((constantModelBoundedConstructible_iff_stacksConstructible l E X _).mpr
      ⟨(internal_completion_stacks_comparison l E X K).mp hc,
        (internal_residue_stacks_comparison l E X K).mpr ⟨hr, ht⟩⟩)

/-- Restriction of scalars along the map from the constant integer ring is an equivalence from
the complexes whose restriction is complete onto the complete complexes, with the inclusion
functors identified with restriction. This is part (2) of
`det-prop-integral-criterion-constant-coefficients` (restriction of scalars is an equivalence
on derived complete objects), transported to the small-site presentation of
`stacksConstructible`; completeness of `K` is read on its restriction as in part (3).
Source: Stacks Tags 0999 and 09C1
(blueprint: det-prop-integral-criterion-constant-coefficients).

Proof: this is `completion_transport`, whose first clause identifies its source property
with `restrictionComplete` and whose target property is `stacksComplete`. -/
theorem restriction_complete_equivalence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) [IsNoetherian X] :
    ∃ e : (restrictionComplete l E X).FullSubcategory ≌ (stacksComplete l E X).FullSubcategory,
      Nonempty (e.functor ⋙ (stacksComplete l E X).ι ≅
        (restrictionComplete l E X).ι ⋙ restriction l E X) := by
  obtain ⟨h, e, α⟩ := completion_transport l E X
  have hA : (fun K ↦ Scheme.IsSfbAdicComplete X (IntegralConstantCompletion.ideal l E)
      ((IntegralConstantModel.derived l E X).functor.obj K)) = restrictionComplete l E X :=
    funext fun K ↦ propext (h K)
  exact hA ▸ ⟨e, α⟩

/-- The criterion part of `det-lem-integral-models-stacks`: a complex over the continuous
integers is bounded constructible iff its restriction is Stacks adic constructible.
Source: blueprint det-lem-integral-models-stacks; Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks).

Proof: transport along `pointComparison` to the internal presentation, apply the two
directions of the integral criterion, and identify completeness and the residue clause by
`internal_completion_stacks_comparison` and `internal_residue_stacks_comparison`. -/
theorem integral_models_stacks_criterion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :
    constantModelBoundedConstructible (integersObj l E) X K ↔
      stacksConstructible l E X ((restriction l E X).obj K) := by
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).hom.hom X)
  let K' := G.mapDerivedCategory.obj K
  let eK : F.mapDerivedCategory.obj K' ≅ K :=
    ((Functor.mapDerivedCategoryCompIso G F).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        ((Mod.comapComp
          (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
          (coefficientMap (IntegralConstantModel.pointComparison l E).hom.hom X)).symm ≪≫
          Mod.comapCongr (by
            rw [← coefficientMap_comp]
            exact (congrArg (upperStarFromPoint X).map (congrArg Mon.Hom.hom
              (IntegralConstantModel.pointComparison l E).inv_hom_id)).trans
              ((upperStarFromPoint X).map_id _)) ≪≫ Mod.comapId _) ≪≫
      Functor.mapDerivedCategoryIdIso _).app K
  have hi := (constantModelConstructibleFiniteTor_wellDefined (integersObj l E) X).2.1
  have hP : constantModelBoundedConstructible (integersObj l E) X K ↔
      constantModelBoundedConstructible (integersObj l E) X (F.mapDerivedCategory.obj K') :=
    ⟨fun h ↦ (constantModelBoundedConstructible _ X).prop_of_iso eK.symm h,
      fun h ↦ (constantModelBoundedConstructible _ X).prop_of_iso eK h⟩
  have hc := constantModelBoundedConstructible_pointComparison_iff l E X K'
  have hint : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K' ↔
      stacksConstructible l E X ((restriction l E X).obj (F.mapDerivedCategory.obj K')) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨h1, h2⟩ := internal_integral_criterion_forward l E X K' h
      exact ⟨(internal_completion_stacks_comparison l E X K').mp h1,
        (internal_residue_stacks_comparison l E X K').mpr h2⟩
    · have h2 := (internal_residue_stacks_comparison l E X K').mp h.2
      exact internal_integral_criterion_reverse l E X K'
        ((internal_completion_stacks_comparison l E X K').mpr h.1) h2.1 h2.2
  have hQ : stacksConstructible l E X ((restriction l E X).obj (F.mapDerivedCategory.obj K')) ↔
      stacksConstructible l E X ((restriction l E X).obj K) :=
    ⟨stacksConstructible_iso l E X ((restriction l E X).mapIso eK),
      stacksConstructible_iso l E X ((restriction l E X).mapIso eK).symm⟩
  exact hP.trans (hc.symm.trans (hint.trans hQ))

/-- Restriction of scalars identifies the bounded constant-model constructible category
with the Stacks adic constructible category, and reflects membership for every complex.
Source: blueprint det-lem-integral-models-stacks; Stacks Tag 09C1
(blueprint: det-lem-integral-models-stacks).

Proof: the criterion is `integral_models_stacks_criterion`. Restriction is an equivalence
from the complexes with complete restriction onto the complete complexes
(`restriction_complete_equivalence`); bounded constructible complexes have complete
restriction and Stacks adic constructible complexes are complete, so the equivalence
restricts to the selected full subcategories with the same functor. -/
theorem integral_models_stacks (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] :
    (∀ K, constantModelBoundedConstructible (integersObj l E) X K ↔
      stacksConstructible l E X ((restriction l E X).obj K)) ∧
    ∃ e : ConstantModelBoundedConstructible (integersObj l E) X ≌
        (stacksConstructible l E X).FullSubcategory,
      Nonempty (e.functor ⋙ (stacksConstructible l E X).ι ≅
        (constantModelBoundedConstructible (integersObj l E) X).ι ⋙ restriction l E X) := by
  have hm := integral_models_stacks_criterion l E X
  refine ⟨hm, ?_⟩
  obtain ⟨e, ⟨α⟩⟩ := restriction_complete_equivalence l E X
  let : (stacksConstructible l E X).IsClosedUnderIsomorphisms :=
    ⟨fun ε h ↦ stacksConstructible_iso l E X ε h⟩
  exact exists_selected_equivalence (constantModelBoundedConstructible (integersObj l E) X)
    (restrictionComplete l E X) (stacksConstructible l E X) (stacksComplete l E X)
    (restriction l E X) e α
    (fun K hK ↦ ((hm K).mp hK).1) (fun _ h ↦ h.1) (fun K _ ↦ hm K)

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
