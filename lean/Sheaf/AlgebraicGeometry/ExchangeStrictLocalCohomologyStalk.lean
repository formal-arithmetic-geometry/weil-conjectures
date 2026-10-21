/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictLocalAbelianTotalExchange
public import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
public import Sheaf.Paper.StrictHenselizationPointEvaluationProperties
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Sheaf.Paper.StrictHenselizationFunctoriality

/-! # Local strict-henselian stalk criterion for exchange

Source: Stacks Project, Tag 0EZU, lemma-base-change-f-star-general-stalks
(blueprint: lem-weil-pbc-exchange-strict-local-cohomology-stalk-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The stalk of degree-q exchange is invertible exactly when the induced map on
strict-local cohomology is bijective. This is the local calculation in the proof of
`isIso_exchange_iff_strictLocalCohomology`; the global conservative-family argument
is kept in that theorem.

Source: Stacks Project, Tag 0EZU, lemma-base-change-f-star-general-stalks.
(blueprint: lem-weil-pbc-exchange-strict-local-cohomology-stalk-criterion).

Proof: equip both strict henselization rings with their canonical strictly henselian
local structures. The evaluation equation makes the supplied ring map local, and the
structural equation gives the pullback square between the strict-local base changes.
Apply the canonical strict-henselization stalk exchange comparison, followed by the
strict-local total cohomology exchange comparison. These give additive equivalences
conjugating the stalk map to the displayed `cohomologyMap`, so bijectivity is preserved.
The residue-field maps are the canonical maps induced by the evaluation homomorphisms;
all compatibility equations follow from `Spec.map` composition and the two hypotheses.
-/
theorem isIso_exchange_stalk_iff_strictLocalCohomology
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (α : (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (((g)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus ⋙
        (f)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (((pullback.snd f g)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
        (pullback.fst f g)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (a : Scheme.strictHenselizationRing (x ≫ f) ⟶ Scheme.strictHenselizationRing x)
    (_ : Scheme.strictHenselizationPointEvaluation (x ≫ f) =
      (Scheme.strictHenselizationPointEvaluation x).comp a.hom)
    (ha : Spec.map a ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
      Scheme.strictHenselizationStructuralMap x ≫ f) :
    IsIso ((Scheme.pointSmallEtale x).sheafFiber.map α) ↔
      Function.Bijective (cohomologyMap
        (pullback.map (Scheme.strictHenselizationStructuralMap x ≫ f) g
          (Scheme.strictHenselizationStructuralMap (x ≫ f)) g
          (Spec.map a) (𝟙 T) (𝟙 S)
          ((Category.comp_id _).trans ha.symm)
          ((Category.comp_id g).trans (Category.id_comp g).symm))
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.snd (Scheme.strictHenselizationStructuralMap (x ≫ f)) g)).obj F) q) := by
  sorry

end AlgebraicGeometry.Etale
