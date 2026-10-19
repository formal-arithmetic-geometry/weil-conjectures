/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Sheaf.FieldTheory.HenselianDVRTameSequence
import Sheaf.GroupTheory.TameEllCoordinate
import Sheaf.RepresentationTheory.KernelInvariantsCohomology

/-!
# Comparison with the tame procyclic quotient

This is the structural comparison used by `DvrGalois`: invariants under the
prime-to-`ell` kernel identify the local Galois cohomology with the cohomology
of the additive `ell`-adic quotient.  The statement is kept separate because
the averaging and injective-resolution argument is itself a lemma of the
local Galois calculation.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Rep

attribute [local irreducible] kernelFixedRepresentation kernelFixedDiscreteRep
  discreteContinuousCohomologyFunctor

/-- The prime-to-`ell` kernel comparison for the absolute Galois group.

Source: blueprint `lem-exc-dvr-galois`, proof steps 1--5.  The proof constructs
the tame quotient, proves exactness of kernel invariants by finite-group
averaging, transports injective resolutions through inflation, and identifies
the resulting quotient with `Multiplicative ℤ_[ell]`.  The finite-module
implication is the fact that taking invariants is a submodule construction.
(blueprint: lem-exc-dvr-galois-comparison)
-/
theorem nonempty_dvr_galois_cohomology_iso
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : IsExcellent R) [IsStrictlyHenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ p)
    (A : Type v) [Ring A] [Finite A]
    (hA : ∃ s : ℕ, (ell ^ s : ℕ) • (1 : A) = 0)
    (M : DiscreteContinuousRep.{v, u, max u w} A
      (Gal(SeparableClosure (FractionRing R)/FractionRing R))) :
    ∃ N : DiscreteContinuousRep.{v, 0, max u w} A (Multiplicative ℤ_[ell]),
      (Finite M.obj.V → Finite N.obj.V) ∧
      ∀ q : ℕ, Nonempty
        (((discreteContinuousCohomologyFunctor
          (Gal(SeparableClosure (FractionRing R)/FractionRing R)) A q).obj M) ≅
        ((discreteContinuousCohomologyFunctor
          (Multiplicative ℤ_[ell]) A q).obj N)) := by
  classical
  obtain ⟨P, hP, _, θ, hcθ, hθ, hker, _, hwild⟩ :=
    IsDiscreteValuationRing.exists_tame_galois_sequence R hR (FractionRing R) p
      (SeparableClosure (FractionRing R))
  let π := (ProfiniteGroup.tameCoordinate p ell hell).comp θ
  have hπ : Function.Surjective π :=
    (ProfiniteGroup.tameCoordinate_surjective p ell hell).comp hθ
  have hcπ : Continuous π :=
    (ProfiniteGroup.tameCoordinate_continuous p ell hell).comp hcθ
  have hwild' : ∀ (Q : Type u) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
      [Finite Q] (f : θ.ker →* Q), Continuous f → Function.Surjective f →
        ∃ n : ℕ, Nat.card Q = p ^ n := by
    subst P
    exact hwild
  have hcop := ProfiniteGroup.tameCoordinate_finite_quotients
    _ p ell hell θ hθ hwild'
  obtain ⟨s, hs⟩ := hA
  refine ⟨kernelFixedDiscreteRep π hπ hcπ M, ?_, ?_⟩
  · intro hM
    unfold kernelFixedDiscreteRep
    exact (inferInstance : Finite (kernelFixedSubmodule π M))
  · intro q
    exact kernelFixed_cohomology_iso.{u, v, w} (A := A) (Multiplicative ℤ_[ell])
      π hπ hcπ ell s hs hcop M q

end Rep
