/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.GenericFibreClosedAvoidance
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import Sheaf.RingTheory.FinitePrimeTranscendentalCoordinate
import Sheaf.TraceFormula.GenericFibreDimensionNeighborhood

/-! # Generic principal coordinate dimension drop

Source: Stacks Project, More on Morphisms, Tag 0GTG, label
`lemma-weak-relative-noether-normalization`, proof lines 8832--8871
(blueprint: lem-trf-generic-principal-coordinate-dimension-drop).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A coordinate lowers fibre dimension over a dense principal open.

Source: Stacks Project, More on Morphisms, Tag 0GTG, label
`lemma-weak-relative-noether-normalization`, proof lines 8832--8871
(blueprint: lem-trf-generic-principal-coordinate-dimension-drop).

Proof plan. Finite type over `ℤ` gives Noetherian rings and finitely many minimal
primes. At the minimal primes whose fibre component has maximal dimension, choose
an element transcendental over the corresponding residue fields. The local fibre
dimension formula and the transcendence-degree tower then show that the locus of
points where the new fibres have dimension at most `d - 1` contains every generic
point, hence is open. Removing its complement lowers the dimensions of the generic
fibres. Shrink over each irreducible component of the base, using generic-fibre
dimension neighbourhood and empty-generic-fibre avoidance, and then use finite prime
avoidance to find one element `f` outside every minimal prime with `D(f)` inside the
resulting dense open. Localizing at `f` identifies the fibres with those over this
principal open. Empty fibres are allowed throughout.
-/
theorem exists_principal_coordinate_dimension_drop
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
    (φ : R →+* S) (d : ℕ) (hd : 1 ≤ d) :
    letI : Algebra R S := φ.toAlgebra
    ∀ hdim : ∀ y : (Scheme.Spec.obj (Opposite.op (CommRingCat.of R))),
      topologicalKrullDim
          ((Scheme.Spec.map (Opposite.op (CommRingCat.ofHom φ))).fiber y) ≤
        (d : WithBot ℕ∞),
    ∃ a : S, ∃ f : R,
      (∀ p : PrimeSpectrum R, p.asIdeal ∈ minimalPrimes R → f ∉ p.asIdeal) ∧
      (∀ y : (Scheme.Spec.obj
          (Opposite.op (CommRingCat.of (Polynomial (Localization.Away f))))),
        topologicalKrullDim
            ((Scheme.Spec.map
                (Opposite.op
                  (CommRingCat.ofHom
                    (Polynomial.eval₂RingHom
                      (IsLocalization.Away.map
                        (Localization.Away f)
                        (Localization.Away (φ f)) φ f)
                      (algebraMap S (Localization.Away (φ f)) a))))).fiber y) ≤
          ((d - 1 : ℕ) : WithBot ℕ∞)) := by
  sorry

end AlgebraicGeometry
