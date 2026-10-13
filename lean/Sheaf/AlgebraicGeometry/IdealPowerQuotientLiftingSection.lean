/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings
import Sheaf.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Lifting sections into ideal-power annihilator quotients

Source: Stacks Project, Properties, Lemmas 01PQ and 01PM.
(blueprint: lem-weil-pbc-ideal-power-quotient-local-lifting-section).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Every section on the ideal complement lifts into an ideal-power annihilator quotient.

Proof: On an affine open write I = (f_1,...,f_t) and F = M~. The condition hann
identifies A_n with Ann_M(I^n)~: localization commutes with this annihilator because
I^n is finitely generated. Hence the cokernel is (M/Ann_M(I^n))~.
Represent the section on D(f_i) as x_i/f_i^k with k positive. Equality on overlaps
means (f_i f_j)^e (f_j^k x_i - f_i^k x_j) = 0. A common e works for all pairs;
replace x_i by f_i^e x_i and k by k+e. Now f_j^k x_i = f_i^k x_j.
Put d = t*(k-1)+1 and K = {x : f_i^k x = 0 for every i}. A degree-d monomial
has an exponent at least k; lower that exponent by k and multiply by x_i.
Multiplication of any resulting relation by f_j^k gives the original relation
multiplied by x_j, so it lies in K. This defines I^d -> M/K, and K is contained
in Ann_M(I^d). The induced map into M/Ann_M(I^d) evaluates to the section.

Choose a finite affine cover of X and use these maps locally. Pass to one degree
using r and q; their equations over the inclusions and projections ensure that
evaluation still represents the same section. On each affine member of a finite
cover of a pairwise overlap, the difference has zero evaluation. Its target is
quasi-coherent by cokernel closure. Apply ideal_power_evaluation_eventually_zero
to this target, then compose with q to kill the difference at a later degree.
Take a common upper bound for the finitely many degrees. Naturality of r and q,
whose composition laws follow by cancellation of monic power inclusions and epic
cokernel projections, preserves the equalities. Glue the maps by sheaf descent;
sectionwise uniqueness proves the required evaluation identity. Quasi-separatedness
is used only for finite affine covers of overlaps. An empty cover uses the unique
zero map; if the ideal is zero use a positive power and the empty complement;
for the unit ideal take degree zero and the map corresponding to the section.

Source: Stacks Project, Properties, Lemma 01PM (affine denominator construction)
and Lemma 01PQ (finite affine gluing), https://stacks.math.columbia.edu/tag/01PM
and https://stacks.math.columbia.edu/tag/01PQ.
(blueprint: lem-weil-pbc-ideal-power-quotient-local-lifting-section). -/
theorem ideal_power_quotient_local_lifting_section
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2)
    (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F)
    (hmono : ∀ n : ℕ, Mono (a n))
    (hqc : ∀ n : ℕ, (A n).IsQuasicoherent)
    (hann : ∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
      s ∈ Set.range ((a n).app W) ↔
        ∀ (W' : X.Opens) (h : W' ≤ W)
          (b : Γ((idealSheafPower ι n).1, W')),
          (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).hom
            (F.presheaf.map (homOfLE h).op s) = 0)
    (hquot : ∀ (n : ℕ) (W : X.Opens), W ≤ U →
      Function.Bijective ((cokernel.π (a n)).app W))
    (q : ∀ (n m : ℕ), n ≤ m → (cokernel (a n) ⟶ cokernel (a m)))
    (hq : ∀ (n m : ℕ) (h : n ≤ m),
      cokernel.π (a n) ≫ q n m h = cokernel.π (a m)) :
    ∀ s : Γ(F, U), ∃ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
      (cokernel.π (a n)).app U s = φ.app U (one n) := by sorry

end AlgebraicGeometry.Scheme
