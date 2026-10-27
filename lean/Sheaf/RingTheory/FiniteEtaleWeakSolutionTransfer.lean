module

public import Sheaf.RingTheory.WeakEppSolution
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.RingTheory.Henselian

import WeilConjectures.FieldTheory.SeparableExtension
import Sheaf.AlgebraicGeometry.FiniteEtaleFiniteLimits
import Sheaf.RingTheory.HenselianFiniteEtaleEquivalence

/-!
# Finite etale transfer of weak Epp solutions

Source: Stacks Project, More on Algebra, Tags 09EN, 09ET, 09EU and 0GLR;
perfect lower residue repair of the final coefficient step of 09ET
(blueprint: lem-sfb-finite-etale-weak-solution-transfer).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y z t

namespace IsDiscreteValuationRing

/-- A weak solution after a finite etale lower coefficient extension gives a weak
solution over the original lower DVR, when its residue field is perfect and the
upper DVR is strictly henselian. No completeness or upper residue perfectness
is assumed; the output is a new finite extension, not the given H over K.

Source: Stacks Project, More on Algebra, Tags 09ET and 09EU, with the perfect
lower residue and normal enlargement repair recorded in the DAG
(blueprint: lem-sfb-finite-etale-weak-solution-transfer).

Proof:
1. By lem-trf-finite-domain-fraction-degree, F/K is finite, hence H/K is finite.
   Enlarge H to a finite normal N/K using
   lem-weil-pbc-finite-extension-in-finite-normal-extension. By
   lem-weil-pbc-finite-algebra-is-integral and lem-sfb-integral-element-tower-descent,
   the integral closures over D and U agree inside H and inside N.
2. Choose an upper H-branch using lem-sfb-dvr-algebraic-normalization-structure.
   Weak solvability identifies its extended maximal ideals. Its lower residue
   is finite over the perfect residue of U and therefore perfect by
   lem-per-algebraic-extension-perfect. Use
   lem-weil-pbc-perfect-field-separating-basis and
   def-weil-pbc-separable-field-extension to obtain the required residue separability.
3. Apply lem-sfb-dvr-index-one-separable-base-change to N/H.
   The identifications and lying-over clause of
   lem-sfb-normalized-finite-coefficient-tower give a good normalized N-branch.
4. By lem-fet-finite-limits, V tensor_U D is finite etale over V.
   By lem-weil-pbc-etale-algebra-over-field-product and
   lem-weil-pbc-henselian-finite-etale-equivalence it is a product of copies of V.
   The given D to V selects a factor. After passing to fraction fields, tensoring
   with N and reducing, the selected factor is the D-normalization tensor factor;
   the other factors may have different F-structures. Use
   lem-weil-pbc-algebra-tensor-pushout-universal-property for these identifications.
   Integral closure respects finite products by multiplying monic equations.
   Thus the good D-branch gives one good branch of the U-normalization.
5. By lem-sfb-normal-coefficient-branch-conjugacy, normality of N/K transports
   that branch to every maximal upper branch, preserving contractions and ideal
   extension. The normalization structure lemma supplies maximal contractions
   and both DVR localizations. Hence N/K is the required weak solution.
-/
theorem exists_weak_solution_of_finite_etale
    (U : Type u) [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    (D : Type v) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (V : Type w) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Algebra U D] [Algebra D V] [Algebra U V] [IsScalarTower U D V]
    [IsLocalHom (algebraMap U D)] [IsLocalHom (algebraMap D V)]
    (hUD : Function.Injective (algebraMap U D))
    (hDV : Function.Injective (algebraMap D V))
    (K : Type x) [Field K] [Algebra U K] [IsFractionRing U K]
    (F : Type y) [Field F] [Algebra D F] [IsFractionRing D F]
    (M : Type z) [Field M] [Algebra V M] [IsFractionRing V M]
    [Algebra K F] [Algebra F M] [Algebra K M] [IsScalarTower K F M]
    [Algebra U F] [IsScalarTower U D F] [IsScalarTower U K F]
    [Algebra D M] [IsScalarTower D V M] [IsScalarTower D F M]
    [Algebra U M] [IsScalarTower U V M] [IsScalarTower U K M]
    [Module.Finite U D] [Algebra.Etale U D]
    [PerfectField (IsLocalRing.ResidueField U)] [IsStrictlyHenselianLocalRing V]
    (H : Type t) [Field H] [Algebra F H]
    (hH : IsWeakEppSolution D V F M H) :
    ∃ (N : Type (max u v w x y z t)) (_ : Field N) (_ : Algebra K N),
      IsWeakEppSolution U V K M N := by
  sorry

end IsDiscreteValuationRing
