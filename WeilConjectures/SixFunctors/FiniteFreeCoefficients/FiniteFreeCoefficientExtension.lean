/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageCoefficientCalculus
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapGeometricSquares

/-! # Finite free coefficient extensions and cofinal levels

The canonical functors and comparison maps are publicly re-exported from the data module.
Source: blueprint, lem-coef-finite-free-extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- Finite free coefficient extensions on the cofinal ramified levels, including all five
canonical comparisons on both small sites, all coefficient cocycles and the scheme-isomorphism
squares. The index `Stage` uses the base uniformizer, so ramification is retained.
Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-free-extension (blueprint: lem-coef-finite-free-extension).

Proof: apply the existing stage_ramification and stage_finiteFree theorems for the
actual base-uniformizer stages. They supply ramification, cofinality and finite
freeness over the quotient rings without a second valuation-ring construction.

Apply the existing normalized_stage_coefficient_calculus to obtain the two normalized
packages. For each stage arrow apply coefficient_map_geometric_squares to
its ring map and the package's normalized pro-etale tensorator. Combine its eight
squares with the two canonical-map equations from the normalized calculus. -/
theorem finite_free_coefficient_extension (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∀ s : Stage l E, ∃ (e : ℕ+) (z : s.integersˣ),
      s.parameter = (z : s.integers) * Padic.coefficientExtensionUniformizer l s.field ^ (e : ℕ) ∧
      (∀ n : ℕ, Ideal.span ({s.parameter} : Set s.integers) ^ n =
        Padic.coefficientExtensionIdeal l s.field ((e : ℕ) * n)) ∧
      ∀ r : ℕ, ∃ n : ℕ+, r ≤ (e : ℕ) * (n : ℕ)) ∧
    (∀ (s t : Stage l E) (a : Arrow s t), s.exponent = t.exponent → a.IsFiniteFree) ∧
    (∀ (T X Z : Scheme.{u})
      [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
      [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
      [QuasiCompact (T ↘ Spec (.of D.k))]
      [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
      [QuasiCompact (X ↘ Spec (.of D.k))]
      [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
      [QuasiCompact (Z ↘ Spec (.of D.k))]
      (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
      (c : Compactification (X ↘ Spec (.of D.k))),
      ∃ (et : Sites.Calculus false l E f i c) (pro : Sites.Calculus true l E f i c),
        Sites.Normalized l E f i c et pro ∧
        ∀ {s t : Stage l E} (a : Arrow s t),
          Sites.DirectGeometry a.ringMap f ∧ Sites.HomGeometry a.ringMap X ∧
          Sites.ClosedGeometry a.ringMap i ∧
          Sites.ExceptionalGeometry a.ringMap c (𝟙_ _) ∧
          Sites.ProDirectGeometry a.ringMap f ∧
          Sites.ProClosedGeometry a.ringMap i ∧
          Sites.ProHomGeometry a.ringMap X (pro.tensorIso a) ∧
          Sites.ProOmegaGeometry a.ringMap c ∧
          (∀ M : Sites.D true s.ring X, Sites.Ctf true s.ring X M →
            pro.closedMap a M = Sites.proClosedMap a.ringMap i M) ∧
          pro.omegaMap a = Sites.proOmegaMap a.ringMap c) := by
  refine ⟨FiniteCoefficientAdjoints.stage_ramification,
    fun _ _ a h ↦ FiniteCoefficientAdjoints.stage_finiteFree a h, ?_⟩
  intro T X Z _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ _ i _ _ c
  obtain ⟨et, pro, hn, hc, hw⟩ :=
    normalized_stage_coefficient_calculus D l _hl E T X Z f i c
  refine ⟨et, pro, hn, ?_⟩
  intro s t a
  obtain ⟨hd, hh, hcl, he, hpd, hpc, hph, hpo⟩ :=
    coefficient_map_geometric_squares s.ring t.ring a.ringMap f i c
      (pro.tensorIso a) (pro.tensor_normalized a)
  exact ⟨hd, hh, hcl, he, hpd, hpc, hph, hpo, hc a, hw a⟩

end WeilConjectures.FiniteFreeCoefficients
