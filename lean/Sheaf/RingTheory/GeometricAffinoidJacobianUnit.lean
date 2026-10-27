module

public import Sheaf.RingTheory.RestrictedSeriesJacobian
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.AffinoidResidualConormalInjective
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.LinearAlgebra.NonzeroMaximalMinorOfInjective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The continuous Jacobian ideal of a geometrically regular affinoid quotient

Source: Temkin, Desingularization of quasi-excellent schemes in characteristic zero,
Proposition 3.3.2, pp. 20--21, and the Jacobian ideal formula preceding it
(blueprint: lem-per-geometric-affinoid-jacobian-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RestrictedSeries

/-- Geometric regularity after all complete isometric field extensions makes the
continuous colon-minor Jacobian ideal the unit ideal. No relative dimension is fixed,
and the quotient may be zero.

Source: Temkin, Proposition 3.3.2, pp. 20--21
(blueprint: lem-per-geometric-affinoid-jacobian-unit).

Proof:
1. The zero quotient is immediate. Otherwise, for a maximal ideal m of C pull it
back to n in the Tate algebra. By lem-per-affinoid-residual-conormal-injective,
the derivative map I/nI to the r-dimensional residue vector space is injective.
2. The classes of the f_j span I/nI. By lem-weil-span-independent-subfamily choose
a subset E forming a basis. Its derivative columns give an injective matrix.
3. Localize at n. The residue of the localized ideal I is I/nI: g/u maps to
(u mod n)⁻¹[g], with inverse [g] mapping to g/1. Thus the chosen relations span
this residue module. Apply lem-weil-pbc-nakayama-local-generators to obtain
that these relations generate the localized ideal.
4. Write each localized relation using those generators. Multiply by the finite
product of denominators, then use the localization zero criterion to kill the
remaining error by an element outside n. Multiplying these elements over all
relations yields a outside n with aI contained in I_E, so a belongs to (I_E:I).
5. By lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor choose rows T with
nonzero determinant modulo n. The Leibniz formula commutes with reduction, so
D_{E,T} is outside n. The empty case has determinant one.
6. The image of a D_{E,T} belongs to the Jacobian ideal and is outside m. Thus no
maximal ideal contains this ideal. By lem-weil-pbc-proper-ideal-contained-in-maximal
it is the unit ideal. E and its cardinality may vary with m. -/
theorem jacobianIdeal_eq_top_of_geometrically_regular
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {r s : ℕ}
    (f : Fin s → MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ)))
    (hgeom : ∀ (L : Type (max u v)) [NormedField L] [IsUltrametricDist L]
      [CompleteSpace L] (φ : K →+* L) (hφ : Isometry φ),
      IsRegularRing
        ((MvPowerSeries.IsRestricted.subring (R := L) (fun _ : Fin r ↦ (1 : ℝ))) ⧸
          relationIdeal (fun j ↦ map r φ hφ (f j)))) :
    jacobianIdeal f = ⊤ := by
  sorry

end RestrictedSeries
