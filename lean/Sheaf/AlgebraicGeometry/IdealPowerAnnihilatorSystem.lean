/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk

/-! # IdealPowerAnnihilatorSystem

Source: Stacks Project, Properties, Lemma 01PQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The annihilator subsheaves of the powers form an increasing quasi-coherent system,
vanish on the specified open, and their cokernel projections are isomorphisms there.

Proof: For each n, form the subsheaf of F consisting of sections killed by every local
section of I^n on every smaller open. Closure under addition, scalars and restriction
is immediate; gluing holds by gluing in F and testing the products locally. This is
an actual subsheaf with its injective inclusion. On affine opens I^n is a finitely
generated ideal J^n and F is the sheaf of a module M. Finite generation permits
clearing one common denominator for all ideal generators, so localization of the
annihilator equals the annihilator of the localized ideal. Thus the subsheaf is
quasi-coherent. The inclusion I^m -> I^n for n <= m makes the annihilators increasing.
On W contained in U, the power inclusion is bijective, so lift 1 and test annihilation
on W itself: every section of the annihilator is zero. Restriction to U preserves
cokernels, and the annihilator restricts to the zero module. Therefore its cokernel
projection restricts to an isomorphism; evaluating on any W contained in U gives the
asserted bijection.

Source: Stacks Project, Properties, Lemma 01PQ and its reduction to Lemma 01PM.
(blueprint: lem-weil-pbc-ideal-power-annihilator-system). -/
theorem ideal_power_annihilator_system
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens)
    (hbij : ∀ (n : ℕ) (W : X.Opens), W ≤ U →
      Function.Bijective ((idealSheafPower ι n).2.app W)) :
    ∃ (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F),
          (∀ n : ℕ, Mono (a n)) ∧
          (∀ n : ℕ, (A n).IsQuasicoherent) ∧
          (∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
            s ∈ Set.range ((a n).app W) ↔
              ∀ (W' : X.Opens) (h : W' ≤ W)
                (b : Γ((idealSheafPower ι n).1, W')),
                (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).hom
                  (F.presheaf.map (homOfLE h).op s) = 0) ∧
          (∀ (n m : ℕ), n ≤ m → ∃ t : A n ⟶ A m, t ≫ a m = a n) ∧
          (∀ (n : ℕ) (W : X.Opens), W ≤ U → Subsingleton Γ(A n, W)) ∧
          (∀ n : ℕ,
            IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map (cokernel.π (a n)))) ∧
          (∀ (n : ℕ) (W : X.Opens), W ≤ U →
            Function.Bijective ((cokernel.π (a n)).app W)) := by sorry

end AlgebraicGeometry.Scheme
