/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTower
import Sheaf.SmoothPurity.FiniteTraceQuotientCounit

/-! # The native finite trace system and its normalized integral reconstruction

The normalized finite orientations retain representing Hom bijections and actual
trace-counit quotient equations.
The same compactification carries their integral reconstruction data.
Source: current blueprint sk-thm-purity-transport, Steps 1--2.
(blueprint: lem-pur-native-normalized-trace-system)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PurityIntegralTower
open AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The native map admits a normalized finite trace system at every positive coefficient
level, with its representing Hom bijections, actual counit quotient equations,
and the integral reconstruction package
for the same compactification.

Proof: apply condensedTateIntegralTower on the native smooth morphism. Its first clause
supplies the finite orientations and quotient data; reindex positive levels by n+1.
The finiteTrace_pairing theorem supplies its representing Hom bijections.
For every pair a ≤ b, apply finiteTrace_quotient_counit to those same quotient data.
Retain the original reconstruction result, which reconstructs precisely these supplied
levels, their root transitions, and their normalized projections. All auxiliary finiteness
and Noetherian witnesses are conclusions. All existential data are extracted in the proof;
no definition chooses a witness, and no unnormalized trace-uniqueness assertion is used.
Source: sk-thm-purity-transport, Steps 1--2, and coefficient reduction in sk-lem-sp-reduction.
(blueprint: lem-pur-native-normalized-trace-system) -/
theorem smoothTrace_nativeSystem
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [Fact (ringChar k ≠ ell)]
    (hchar : 0 < ringChar k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∃ (hfq : QuasiCompact f) (hfs : IsSeparated f) (c : Compactification f)
      (hX : IsNoetherian X) (hY : IsNoetherian Y),
      let := hfq
      let := hfs
      let := c.hasCompactification
      let := hX
      let := hY
      ReconstructionResult ell f d hfq hfs c hX hY ∧
      ∃ (s : ∀ n : ℕ, Level ell (n + 1) f d)
        (r : ∀ (b a : ℕ) (hab : a ≤ b),
          ReductionData (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
            f d (s b) (s a)),
        (∀ (n : ℕ) (K : Etale.DerivedCategoryModule (coefficient.{u} ell (n + 1)) Y),
          Etale.DerivedCategory.boundedConstructibleFiniteTor (coefficient ell (n + 1)) Y K →
          ∀ Q : Etale.DerivedCategoryModule (coefficient.{u} ell (n + 1)) X,
            Function.Bijective
              (fun v : Q ⟶ (puritySource (coefficient ell (n + 1)) f
                (line (coefficient ell (n + 1)) (ell ^ (n + 1))
                  (CharP.cast_eq_zero _ _) X d)).obj K ↦
                (Etale.rightDerivedLowerShriek
                  (ModuleCat.{u + 1} (coefficient ell (n + 1))) f).map v ≫
                  trace (coefficient ell (n + 1)) f
                    (line (coefficient ell (n + 1)) (ell ^ (n + 1))
                      (CharP.cast_eq_zero _ _) X d) (s n).alpha K)) ∧
        ∀ (b a : ℕ) (hab : a ≤ b),
          let A := coefficient.{u} ell (b + 1)
          let B := coefficient.{u} ell (a + 1)
          let phi := FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)
          let LA := line A (ell ^ (b + 1)) (CharP.cast_eq_zero _ _) X d
          let LB := line B (ell ^ (a + 1)) (CharP.cast_eq_zero _ _) X d
          ∀ (K : proCategory A Y), IsCtf A Y K →
            (proCompact B f).map
                ((proScalar phi X).map (proGamma A f LA (s b).alpha K)) ≫
              proCompactCoefficientInverse phi f ((exceptional A f).obj K) ≫
                (proScalar phi Y).map (proCounit A f K) =
            (proCompact B f).map (proLambda f d (r b a hab).twist K) ≫
              proTrace B f LB (s a).alpha ((proScalar phi Y).obj K) := by
  obtain ⟨hfq, hfs, c, hX, hY, hrec⟩ :=
    condensedTateIntegralTower ell k hchar f d
  refine ⟨hfq, hfs, c, hX, hY, ?_⟩
  let := hfq
  let := hfs
  let := c.hasCompactification
  let := hX
  let := hY
  have hs : FiniteSmoothSystem ell f d := by
    unfold ReconstructionResult at hrec
    exact hrec.1
  obtain ⟨level, reduction, _⟩ := hs
  let s (n : ℕ) := level (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let r (b a : ℕ) (hab : a ≤ b) :=
    reduction (b + 1) (a + 1) (Nat.succ_le_succ (Nat.zero_le a))
      (Nat.add_le_add_right hab 1)
  refine ⟨hrec, s, r, ?_, ?_⟩
  · intro n K hK Q
    exact finiteTrace_pairing f d (s n) K hK Q
  · intro b a hab
    dsimp only
    intro K hK
    exact finiteTrace_quotient_counit f d (r b a hab) K hK

end AlgebraicGeometry.ProEtale.CondensedRing
