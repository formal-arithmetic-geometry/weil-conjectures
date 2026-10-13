/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.FormalGlueingH0Localization
import Sheaf.Paper.FormalGlueingCanonicalMaps
import Sheaf.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# An injective approximation to formal glueing data

Source: Stacks Project, More on Algebra, Proposition 05ER.
(blueprint: lem-weil-pbc-formal-glueing-injective-approximation).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

/-- Compatible sections give a morphism with bijective charts, injective prime map,
and ideal-power torsion prime cokernel.
Source: Stacks Project, More on Algebra, Proposition 05ER, second paragraph.
(blueprint: lem-weil-pbc-formal-glueing-injective-approximation).
Proof: take H to be the submodule of compatible families in the prime module times
all charts. Extend each chart projection across localization using the H0 localization
lemma. Extend the prime projection by the tensor universal property. The fraction
formulas for comparison and interchange show these maps satisfy the two morphism
relations: on a pure tensor fraction the prime relation is the defining prime/chart
relation of H, and on a double fraction the chart relation is its overlap relation.
The localized prime map is bijective because it is conjugate to the scalar extension
of the chart map. Localization exactness therefore makes its kernel and cokernel
vanish in every chart. For each element choose an annihilating power of each f i;
the sum of those exponents kills the element by the whole generated ideal power.
For a kernel element, torsion-submodule base change writes it as 1 tensor h for an
ideal-power torsion h in H. Its prime projection is zero. Its chart projections are
zero since torsion localizes to zero and the localized chart projections are
bijective. Thus h is zero as a compatible family, proving prime injectivity.
The construction is in universe max u v w, using a finite product and a submodule.
If t is zero, H is the prime module and the same torsion comparison proves the
prime map injective; the empty chart conclusions are vacuous. If the ideal is the
unit ideal, the asserted torsion cokernel is zero. -/
theorem exists_injective_approximation {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f)
    (hobj : (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))))
    (hflat : φ.Flat)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map))
    (X : Data.{u, v, max u v w} φ f) :
    ∃ (H : ModuleCat.{max u v w} R) (ψ : Can.obj H ⟶ X),
      Function.Injective ψ.prime ∧ (∀ i, Function.Bijective (ψ.chart i)) ∧
      ∀ x : restrict φ (ModuleCat.of S (X.M' ⧸ LinearMap.range ψ.prime)),
        ∃ n : ℕ, 1 ≤ n ∧ ∀ r ∈ (Ideal.span (Set.range f)) ^ n, r • x = 0 := by sorry

end FormalGlueing
