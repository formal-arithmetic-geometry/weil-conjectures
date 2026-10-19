/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.AdicCoefficientDatumCompleted
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Sequential derived inverse limits over completed coefficients

Source: blueprint, proper base change, order 1240; Stacks Tags 07KC and 08TC
(blueprint: def-weil-pbc-derived-inverse-limit).

The notation is a distinguished Roos triangle, not a functorial choice of its vertex.
Evaluation of a derived strict tower retains every transition through localization.

## Main definitions

* `adicDatumEvaluateDerived`: termwise derived evaluation of strict towers.
* `CompletedSequentialDerivedLimit`: the distinguished Roos triple.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- Exact countable products of modules over the completed coefficient sheaf.
Source: order 1240; Bhatt--Scholze 4.2.8
(blueprint: def-weil-pbc-derived-inverse-limit).
Proof: apply countableProducts_exact to A_T. Its product-of-epis clause, together
with sectionwise kernels, gives exactness of the countable product functor. -/
theorem adicDatumCountableAB4Star : CountableAB4Star (adicDatumModules T d) := by
  have : (lim (J := Discrete ℕ) (C := adicDatumModules T d)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (ProEt.countableProducts_exact.{t, t, 0} T
          (adicDatumRing T d)).2.2 ℕ (fun n ↦ F.obj ⟨n⟩)
            (fun n ↦ G.obj ⟨n⟩) (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi (adicDatumModules T d) (Discrete ℕ)
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat _

/-- Countable products in D(Mod(A_T)), canonically up to their limit property.
Source: order 1240; Tag 07KC (blueprint: def-weil-pbc-derived-inverse-limit). -/
instance adicDatumDerivedCountableProducts : HasCountableProducts (adicDatumDerived T d) :=
  letI := HasDerivedCategory.standard (adicDatumModules T d)
  letI := adicDatumCountableAB4Star T d
  (derivedCategory_countableProducts_core.{0, t + 2, t + 1, t + 2}
    (adicDatumModules T d)).choose

/-- Termwise localization of a strict tower complex, with all its transition maps.
Source: order 1240 (blueprint: def-weil-pbc-derived-inverse-limit). -/
def adicDatumEvaluateComplex : CochainComplex (adicDatumTowers T d) ℤ ⥤
    (ℕᵒᵖ ⥤ adicDatumDerived T d) :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight _ _ _).obj (completedConstantQ _)

/-- Evaluation and termwise localization invert quasi-isomorphisms of strict towers.
Source: order 1240; Tag 015F (blueprint: def-weil-pbc-derived-inverse-limit).
Proof: evaluation is exact, so every component of a tower quasi-isomorphism is a
quasi-isomorphism. Localization makes each component invertible, and a natural
transformation with all components invertible is invertible. -/
theorem adicDatumEvaluateComplex_inverts :
    (HomologicalComplex.quasiIso (adicDatumTowers T d) (ComplexShape.up ℤ)).IsInvertedBy
      (adicDatumEvaluateComplex T d) := by
  intro K L f hf
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  have : QuasiIso
      ((((CategoryTheory.evaluation ℕᵒᵖ (adicDatumModules T d)).obj n).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) :=
    (HomologicalComplex.quasiIso_iff_evaluation f).mp hf n
  change IsIso ((completedConstantQ _).map
    ((((CategoryTheory.evaluation ℕᵒᵖ (adicDatumModules T d)).obj n).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f))
  infer_instance

/-- The canonical localization lift of termwise tower evaluation.
Source: order 1240 (blueprint: def-weil-pbc-derived-inverse-limit). -/
def adicDatumEvaluateDerived : adicDatumTowerDerived T d ⥤
    (ℕᵒᵖ ⥤ adicDatumDerived T d) :=
  Localization.lift (adicDatumEvaluateComplex T d) (adicDatumEvaluateComplex_inverts T d)
    (completedConstantQ _)

/-- A sequential derived inverse limit is precisely a vertex and maps whose
Roos triangle is distinguished. It is read on the evaluated diagram of a strict
derived tower; the predicate itself needs only that diagram and makes no choice.
Source: order 1240; Tag 08TC (blueprint: def-weil-pbc-derived-inverse-limit). -/
structure CompletedSequentialDerivedLimit (B : ℕᵒᵖ ⥤ adicDatumDerived T d) where
  obj : adicDatumDerived T d
  p : obj ⟶ ∏ᶜ (fun n : ℕ ↦ B.obj (op n))
  δ : (∏ᶜ (fun n : ℕ ↦ B.obj (op n))) ⟶ obj⟦(1 : ℤ)⟧
  distinguished : IsDerivedLimitTriangle
    (fun n : ℕ ↦ B.map (homOfLE (Nat.le_succ n)).op) obj p δ

end AlgebraicGeometry.Scheme
