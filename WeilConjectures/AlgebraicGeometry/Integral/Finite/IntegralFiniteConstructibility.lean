/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteConstructibilityTriangle
import WeilConjectures.AlgebraicGeometry.Integral.Finite.IntegralFiniteFiltrationTriangle

/-! # Finite coefficient constructibility -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesDerived

private theorem boundedConstructible_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {L M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (e : L ≅ M)
    (h : constantModelBoundedConstructible Λ X L) :
    constantModelBoundedConstructible Λ X M := by
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
  exact ObjectProperty.prop_of_iso _ e h

private theorem pairedInduction (P Q : ℕ → Prop) (h₀ : P 0 ∧ Q 0)
    (step : ∀ n, P n ∧ Q n → P (n + 1) ∧ Q (n + 1)) :
    (∀ n, P n) ∧ (∀ n, Q n) := by
  have h : ∀ n, P n ∧ Q n := Nat.rec h₀ step
  exact ⟨fun n ↦ (h n).1, fun n ↦ (h n).2⟩

private theorem localOnStratum_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (S : Scheme.Stratification X) (i : Fin S.n)
    {L M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (e : L ≅ M)
    (h : finiteLocalModelsOnStratum Λ X S i L) :
    finiteLocalModelsOnStratum Λ X S i M := by
  intro q
  obtain ⟨U, hU⟩ := h q
  refine ⟨U, fun j ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU j
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f j)).mapIso
    ((CondensedRing.upperStar Λ (S.immersion i)).mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso e.symm)) ≪≫ eP⟩⟩

private theorem propagateFinite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (L : (n : ℕ) → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n)))
    (triangles : ∀ n : ℕ, ∃ Δ : CategoryTheory.Pretriangulated.Triangle
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X (n + 1)))),
      Δ ∈ distTriang _ ∧
      Nonempty (Δ.obj₁ ≅
        (Mod.comap (integralResidueTransition l E X (n + 1))).mapDerivedCategory.obj (L 0)) ∧
      Nonempty (Δ.obj₂ ≅ L (n + 1)) ∧
      Nonempty (Δ.obj₃ ≅
        (Mod.comap (AdicCompletion.transition l E X n)).mapDerivedCategory.obj (L n)))
    (h₀ : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X (L 0)) :
    (∀ n, constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) X (L n)) ∧
    (∀ (S : Scheme.Stratification X) (i : Fin S.n),
      integralFiniteLocalOnStratum l E X 0 S i (L 0) →
      ∀ n, integralFiniteLocalOnStratum l E X n S i (L n)) := by
  let P (n : ℕ) := constantModelBoundedConstructible
    (DerivedNakayama.quotientRing l E (n + 1)) X (L n)
  let Q (n : ℕ) := ∀ (S : Scheme.Stratification X) (i : Fin S.n),
    integralFiniteLocalOnStratum l E X 0 S i (L 0) →
    integralFiniteLocalOnStratum l E X n S i (L n)
  have h := pairedInduction P Q ⟨h₀, fun _ _ h ↦ h⟩ (by
    intro n ih
    obtain ⟨Δ, hΔ, ⟨e₀⟩, ⟨e₂⟩, ⟨eₙ⟩⟩ := triangles n
    obtain ⟨hc, hs⟩ := integral_finite_constructibility_triangle l E X n
      (L 0) (L n) Δ hΔ e₀ eₙ h₀ ih.1
    refine ⟨boundedConstructible_iso (DerivedNakayama.quotientRing l E (n + 1 + 1)) X e₂ hc,
      fun S i hS ↦ ?_⟩
    exact localOnStratum_iso (DerivedNakayama.quotientRing l E (n + 1 + 1)) X S i e₂
      (hs S i hS (ih.2 S i hS)))
  exact ⟨h.1, fun S i hS n ↦ h.2 n S i hS⟩

/-- Constructibility and a fixed stratum propagate from the residue reduction.

Source: blueprint latest, lemma-bounds-finite-reductions, first paragraph
(blueprint: lemma-bounds-finite-reductions--1).

Proof: write B for the pulled-back continuous integer ring and A_n for the finite
quotient of exponent n+1. Resolve K by a K-flat complex with flat terms. The regular
uniformizer coefficient sequences, tensored termwise with that representative, give
short exact sequences of complexes. Their maps are linear over A_(n+1): restriction
from this quotient to B is full, since B -> A_(n+1) is an epimorphism and tensoring
preserves epimorphisms. Lift the complexes and maps through this exact faithful
restriction and pass to their distinguished triangles. Their outer terms are the
previous reduction and the first reduction, restricted along the finite coefficient
maps. The finite internal/ordinary comparison respects these coefficient maps and
identifies bounded constructibility with the ordinary bounded constructible class.
Finite scalar restriction preserves that class and its distinguished-triangle closure
therefore gives bounded constructibility by induction. For the last assertion apply
exact inverse image along the given immersion to these same triangles; it commutes
with cohomology. Over each finite coefficient ring, sheaves with finite constant
local models form a weak Serre class, so the long exact sequence and induction give
finite constant local models on this very stratum, without changing its immersion.
Return through the finite-model comparison. No completeness or Tor bound is used. -/
theorem integral_finite_constructibility
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (h₁ : constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E 1) X
      ((AdicCompletion.derivedReduction l E X 0).obj K)) :
    (∀ n : ℕ, constantModelBoundedConstructible
      (DerivedNakayama.quotientRing l E (n + 1)) X
      ((AdicCompletion.derivedReduction l E X n).obj K)) ∧
    (∀ (S : Scheme.Stratification X) (i : Fin S.n),
      integralFiniteLocalOnStratum l E X 0 S i
        ((AdicCompletion.derivedReduction l E X 0).obj K) →
      ∀ n, integralFiniteLocalOnStratum l E X n S i
        ((AdicCompletion.derivedReduction l E X n).obj K)) := by
  exact propagateFinite l E X
    (fun n ↦ (AdicCompletion.derivedReduction l E X n).obj K)
    (fun n ↦ integral_finite_filtration_triangle l E X K n) h₁

end AlgebraicGeometry.ProEtale
