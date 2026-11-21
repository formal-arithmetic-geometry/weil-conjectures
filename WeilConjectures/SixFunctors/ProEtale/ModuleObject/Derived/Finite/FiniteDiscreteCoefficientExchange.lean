/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRealizationFunctor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientExchangeFromComparisons

/-! # Realization of finite discrete coefficient sheaves and exchange steps


## References

* Bhatt--Scholze, Proposition 5.3.2, Lemmas 5.4.1 and 5.4.3
* Stacks Project, Tag 09AK
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_finiteDiscreteCoefficientExchange
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

set_option linter.unusedVariables false in
/-- Finite discrete realization on constructible sheaves and on the three exchange steps. -/
theorem finiteDiscreteExchange_coefficientRealization [DiscreteTopology B] [Finite B]
    (hB : (ℓ : B) = 0) (sq : CommSq g' f' f g)
    (eR : ∀ T : Scheme.{u},
      Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
          condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
    (heR : ∀ T : Scheme.{u}, IsMonHom (eR T).hom)
    (hEncoding : ∀ T : Scheme.{u},
      ∃ G : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (RingCat.of (ULift.{u + 1} B) : RingCat.{u + 1}))) ⥤
            Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} B)),
        G.IsEquivalence ∧ Nonempty (G ⋙
          sheafCompose (Scheme.ProEt.topology T)
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) ≅
          Mod.forget (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj
              (RingCat.of (ULift.{u + 1} B) : RingCat.{u + 1}))))) :
    haveI : Fact (IsNilpotent (ℓ : B)) := ⟨⟨1, by rw [pow_one]; exact hB⟩⟩
    ∃ (E0 : FiniteDiscreteProEtaleSheaves B X ≌ FiniteDiscreteInternalModules B X)
      (E1 : FiniteDiscreteProEtaleSheaves B Y' ≌ FiniteDiscreteInternalModules B Y'),
      (∀ M : FiniteDiscreteInternalModules B X,
        ProEtale.IsConstructibleModuleObject
          (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) M →
        (ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} B)] ⋙ E0.functor).essImage M) ∧
      finiteDiscreteExchangeSteps B ℓ k sq
        (finiteDiscreteRealization B X E0) (finiteDiscreteRealization B Y' E1) := by
  have _ := heR
  have _ := hEncoding
  obtain ⟨e, he⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  let := he
  obtain ⟨G, hG, hforget⟩ := internalModuleAb_equivalence (ULift.{u + 1} B)
  let := hG
  let E := finiteDiscreteCoefficientEquivalence B e G hforget
  refine ⟨E X, E Y', ?_, ?_⟩
  · intro M hM
    obtain ⟨A, _, ⟨i⟩⟩ :=
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj (ULift.{u + 1} B)
        (finiteDiscreteCoefficient_constructible B e G hforget X M hM)
    exact ⟨A, ⟨(E X).functor.mapIso i ≪≫ (E X).counitIso.app M⟩⟩
  · obtain ⟨P⟩ := finiteDiscreteCoefficient_derivedComparisonData B e G hforget
    exact coefficientComparisonData_exchangeSteps B ℓ k hB sq
      (fun T ↦ finiteDiscreteRealization B T (E T)) (P.toComparisonData B)

end AlgebraicGeometry.ProEtale.CondensedRing
