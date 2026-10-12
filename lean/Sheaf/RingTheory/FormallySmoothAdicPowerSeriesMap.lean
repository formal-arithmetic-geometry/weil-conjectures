/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Sheaf.RingTheory.ExistsCoefficientSubring
import Sheaf.RingTheory.ExistsLiftOfFieldCharP
import Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete

/-!
# A power series comparison map for a complete adically formally smooth algebra

Source: Stacks Project, More on Algebra, Tag 07EI (lemma-fs-implies-regular),
the prime-field reduction and the construction of the map to the power series ring.
(blueprint: lem-weil-pbc-fs-adic-power-series-comparison-map).
-/

@[expose] public section

universe u v

namespace Algebra

/-- The comparison map constructed in the proof of Stacks Tag 07EI induces a surjection
on residues and extends the maximal ideal to the variables' ideal.
(blueprint: lem-weil-pbc-fs-adic-power-series-comparison-map)

Proof: First restrict formal smoothness from k to its prime field k₀. For a square-zero
lifting problem, lift the map from k using formal smoothness of characteristic-zero
field extensions, or the positive-characteristic field lifting theorem. Give the target
its k-algebra structure through this lift, and use the assumed adic formal smoothness
of A. A lift of a map killing m^q kills m^(2q).
By Cohen's coefficient-subring theorem, complete A contains a copy of its residue field K:
in equal characteristic the coefficient subring's maximal ideal (p) is zero. Identify it
with K by reduction. Choose lifts x₁,...,x_d of a K-basis of m/m². Nakayama identifies d
with m.spanFinrank. Set T = K[[X₁,...,X_d]] and N = (X₁,...,X_d). The coefficient field
and tangent basis identify A/m² and T/N², by sending x_i to X_i and fixing K.
Starting with the resulting map A → T/N², lift recursively to T/N^(r+2) from T/N^(r+1).
The kernels are square-zero because 2r+2 ≥ r+2 for r ≥ 1. Each lift kills a power of m,
so the adic formal smoothness over k₀ applies at every stage. Completeness of T supplies
a ring map f : A → T. Its reduction modulo N² is the prescribed isomorphism, although
f need not be K-linear. In particular the residue map is surjective, f(m) lies in N,
and the classes of f(x_i) span N/N². Nakayama in the Noetherian local ring T gives
N = (f(x_i)); thus Ideal.map f m = N. This proves both claims without claiming that
f itself is surjective or making any dimension comparison. Source: Tag 07EI, proof,
from the prime-field reduction through the construction of f and its tangent map. -/
theorem exists_powerSeries_comparison_of_formallySmoothAdic (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (h : FormallySmoothAdic k A (IsLocalRing.maximalIdeal A)) :
    ∃ f : A →+* MvPowerSeries (Fin (IsLocalRing.maximalIdeal A).spanFinrank)
        (IsLocalRing.ResidueField A),
      Ideal.map f (IsLocalRing.maximalIdeal A) =
        Ideal.span (Set.range (fun i : Fin (IsLocalRing.maximalIdeal A).spanFinrank ↦
          (MvPowerSeries.X i : MvPowerSeries (Fin (IsLocalRing.maximalIdeal A).spanFinrank)
            (IsLocalRing.ResidueField A)))) ∧
      Function.Surjective ((Ideal.Quotient.mk (Ideal.map f (IsLocalRing.maximalIdeal A))).comp
        f) := by sorry

end Algebra
