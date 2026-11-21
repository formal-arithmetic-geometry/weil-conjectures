/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CoefficientMorphism
public import WeilConjectures.TraceFormula.IntegralCoefficientComparison
public import WeilConjectures.TraceFormula.IntegralTraceTransport

/-!

# The trace formula with `𝒪_E`-coefficients

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding
  PadicIntegersRingObj.boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {E : PadicAlgCl.FiniteIntermediateField ℓ}
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- A right dual transported along an isomorphism. -/
@[reducible]
def hasRightDualOfIso {C : Type*} [Category C] [MonoidalCategory C] {A B : C} (e : A ≅ B)
    [HasRightDual B] : HasRightDual A :=
  { rightDual := Bᘁ, exact := exactPairingCongrLeft e }

/-- If an additive functor `F` is injective on `A ⟶ B` and `e ≫ F f ≫ e' = ∑ᵢ e ≫ F tᵢ ≫ e'` for an
epimorphism `e` and a monomorphism `e'`, then `f = ∑ᵢ tᵢ`. -/
lemma eq_sum_of_map_eq_sum {C D : Type*} [Category* C] [Preadditive C] [Category* D]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {A B : C} {A' B' : D} (e : A' ⟶ F.obj A)
    (e' : F.obj B ⟶ B') [Epi e] [Mono e'] (hF : ∀ g : A ⟶ B, F.map g = 0 → g = 0) {ι : Type*}
    (s : Finset ι) (f : A ⟶ B) (t : ι → (A ⟶ B))
    (h : e ≫ F.map f ≫ e' = ∑ i ∈ s, e ≫ F.map (t i) ≫ e') : f = ∑ i ∈ s, t i := by
  rw [← Preadditive.comp_sum, ← Preadditive.sum_comp, ← Functor.map_sum] at h
  have h' := (cancel_mono e').1 ((cancel_epi e).1 h)
  rw [← sub_eq_zero]
  exact hF _ (by rw [Functor.map_sub, h', sub_self])

namespace PadicIntegersRingObj

theorem trace_frobeniusCompactOperator_eq_sum [IsAlgClosed k] {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p)
    [IsProper Φ.left] (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (θ : (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ Φ).obj K ⟶ K)
    {m : ℕ} (hm : 1 ≤ m) [Fintype (FixedPoint Φ m)]
    [hK : HasRightDual ((boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).obj K)]
    [hx : ∀ x : RationalPoint X, HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ x).obj K)] :
    trace (frobeniusCompactOperator θ m) =
      ∑ x : FixedPoint Φ m, trace (graphStalkMap K (frobeniusIterate Φ m)
        (frobeniusCoefficientIterate θ m) x.1 x.2) := by
  let hTop : HasRightDual ((boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).obj
      ((boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).obj K)) :=
    { rightDual := _
      exact := ExactPairing.map (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)) _
        ((boundedConstructibleLowerShriek ℓ E.1 (toPoint X)).obj K)ᘁ }
  let hTst : ∀ x : RationalPoint X, HasRightDual
      ((boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).obj
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ x).obj K)) :=
    fun x ↦
      { rightDual := _
        exact := ExactPairing.map (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)) _
          ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E.1) ℓ x).obj K)ᘁ }
  let hQop : HasRightDual ((CondensedRing.boundedConstructibleLowerShriek ℓ (toPoint X)).obj
      ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K)) :=
    hasRightDualOfIso (lowerShriekIntegersToPadicAlgClObjIso E (toPoint X) K).symm
  let hQst : ∀ x : RationalPoint X, HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K)) :=
    fun x ↦ hasRightDualOfIso (upperStarIntegersToPadicAlgClObjIso E x K).symm
  have hQ := CondensedRing.trace_frobeniusCompactOperator_eq_sum ℓ hΦ
    ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K)
    (frobeniusCoefficientIntegersToPadicAlgCl E θ) hm
  have hop : trace ((boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map
        (frobeniusCompactOperator θ m)) =
      trace (CondensedRing.frobeniusCompactOperator ℓ
        (frobeniusCoefficientIntegersToPadicAlgCl E θ) m) :=
    trace_eq_of_iso (lowerShriekIntegersToPadicAlgClObjIso E (toPoint X) K) _ _
      (map_frobeniusCompactOperator_integersToPadicAlgCl E θ m)
  have hst : ∀ x : FixedPoint Φ m,
      trace ((boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)).map
        (graphStalkMap K (frobeniusIterate Φ m) (frobeniusCoefficientIterate θ m) x.1 x.2)) =
      trace (Correspondence.graphStalkMap ((boundedConstructibleIntegersToPadicAlgCl ℓ E X).obj K)
        (frobeniusIterate Φ m)
        (frobeniusCoefficientIterate (frobeniusCoefficientIntegersToPadicAlgCl E θ) m) x.1 x.2) := by
    intro x
    refine trace_eq_of_iso (upperStarIntegersToPadicAlgClObjIso E x.1 K) _ _ ?_
    rw [map_graphStalkMap_integersToPadicAlgCl,
      map_frobeniusCoefficientIterate_integersToPadicAlgCl, Iso.inv_hom_id_assoc]
  have key := (trace_boundedConstructibleIntegersToPadicAlgCl_map E (point k) (hTA := hTop)
      (frobeniusCompactOperator θ m)).symm.trans ((hop.trans hQ).trans (Finset.sum_congr rfl
        fun x _ ↦ ((hst x).symm.trans (trace_boundedConstructibleIntegersToPadicAlgCl_map E
          (point k) (hA := hx x.1) (hTA := hTst x.1) _))))
  exact eq_sum_of_map_eq_sum (boundedConstructibleIntegersToPadicAlgCl ℓ E (point k)) _ _
    (eq_zero_of_boundedConstructibleIntegersToPadicAlgCl_map_eq_zero E) _ _ _ key

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
