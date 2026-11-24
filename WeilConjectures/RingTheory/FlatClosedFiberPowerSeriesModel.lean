/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.ClosedFiberEquationRemoval
import WeilConjectures.RingTheory.FlatClosedFiberKernelRigidity

/-! # Removing the equations of a regular closed fibre

For a flat local map `A → B` of Noetherian local rings with formally smooth closed fibre and a
compatible Cohen presentation, the equations of the closed fibre can be removed: `B` becomes
the base change `T ⊗_R A` of a power-series ring `T` along the presentation `R → A`.

## Main results

* `RingHom.exists_flat_closedFiber_powerSeries_model`

## References

* [Stacks Project, Tag 07NQ](https://stacks.math.columbia.edu/tag/07NQ), proof of (2)
  implies (3), through the isomorphism `S ⊗_R A → B`.
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace RingHom

/-- Given a compatible power-series presentation of a flat local map `A → B` with formally
smooth closed fibre, there is a power-series ring `T` over the same coefficients with a
surjection `T → B` and a local map `R → T` from the base power-series ring, compatible
with `R → A`, such that `ker(T → B) = ker(R → A) T` (so `B ≅ T ⊗_R A`), the parameters of `R`
extend to a regular system of parameters of `T`, and the closed fibre of `R → T` is formally
smooth. No relative formal smoothness of `R → T` or of `A → B` is asserted. -/
theorem exists_flat_closedFiber_powerSeries_model
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (hflat : f.Flat)
    (ΛR ΛS : Type w) [CommRing ΛR] [CommRing ΛS] (n m : ℕ)
    [IsRegularLocalRing (MvPowerSeries (Fin n) ΛR)]
    [IsRegularLocalRing (MvPowerSeries (Fin m) ΛS)]
    (q : MvPowerSeries (Fin n) ΛR →+* A) [IsLocalHom q]
    (b : MvPowerSeries (Fin m) ΛS →+* B) [IsLocalHom b]
    (i : MvPowerSeries (Fin n) ΛR →+* MvPowerSeries (Fin m) ΛS) [IsLocalHom i]
    (hq : Function.Surjective q) (hb : Function.Surjective b)
    (hcomm : b.comp i = f.comp q)
    (t : List (MvPowerSeries (Fin n) ΛR))
    (z : List (MvPowerSeries (Fin m) ΛS))
    (ht : IsRegularSystemOfParameters t)
    (hz : IsRegularSystemOfParameters (t.map i ++ z))
    (hcoeff : (IsField ΛR ∧ IsField ΛS ∧ CharZero ΛR ∧ CharZero ΛS) ∨
      ∃ p : ℕ, p.Prime ∧ IsCohenRing p ΛR ∧ IsCohenRing p ΛS ∧
        t.head? = some (p : MvPowerSeries (Fin n) ΛR)) :
    letI : Algebra A B := f.toAlgebra
    let I : Ideal B := Ideal.map f (maximalIdeal A)
    letI : Algebra (A ⧸ maximalIdeal A) (B ⧸ I) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal A ≤ I.comap (algebraMap A B))
    Algebra.FormallySmoothAdic (A ⧸ maximalIdeal A) (B ⧸ I)
        (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B)) →
    ∃ m' : ℕ, let T := MvPowerSeries (Fin m') ΛS
      ∃ (_ : IsRegularLocalRing T)
        (v : T →+* B) (j : MvPowerSeries (Fin n) ΛR →+* T),
        Function.Surjective v ∧ IsLocalHom j ∧
        v.comp j = f.comp q ∧ RingHom.ker v = (RingHom.ker q).map j ∧
        ∃ y : List T, IsRegularSystemOfParameters (t.map j ++ y) ∧
          (let R := MvPowerSeries (Fin n) ΛR
           letI : Algebra R T := j.toAlgebra
           let L : Ideal T := (maximalIdeal R).map j
           letI : Algebra (R ⧸ maximalIdeal R) (T ⧸ L) :=
             Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
               maximalIdeal R ≤ L.comap (algebraMap R T))
           Algebra.FormallySmoothAdic (R ⧸ maximalIdeal R) (T ⧸ L)
             ((maximalIdeal T).map (Ideal.Quotient.mk L))) := by
  dsimp only
  intro hsmooth
  obtain ⟨m', hT, v, j, hv, hj, hcomm', hker, y, hparams, hsmooth'⟩ :=
    exists_closedFiber_equation_removal A B f ΛR ΛS n m q b i
      hq hb hcomm t z ht hz hcoeff hsmooth
  let := hT
  let := hj
  have hker' : RingHom.ker v = (RingHom.ker q).map j :=
    ker_eq_map_of_flat_of_ker_le_maximal q f hflat j v hq hv hcomm' hker
  exact ⟨m', hT, v, j, hv, hj, hcomm', hker', y, hparams, hsmooth'⟩

end RingHom
