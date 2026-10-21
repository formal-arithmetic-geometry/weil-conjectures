module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceOverField
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
import WeilConjectures.AlgebraicGeometry.AlternatingCechComputes
import Sheaf.AlgebraicGeometry.ProjectiveSpace.TwistCechMonomialDecomposition
import Sheaf.AlgebraicGeometry.ProjectiveSpace.ExponentCechHomology
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Differentials

/-! # Cohomology and canonical sheaf of projective space over a field

Source: blueprint main-20261015, sec-picard-framework/sk-thm-picard-pn/_section.md;
Stacks Project, Tag 01XT, lemma-cohomology-projective-space-over-ring and equation-identify.
(blueprint: sk-thm-picard-pn)

Cohomology is the right derived functor in module sheaves specified by
`pqf-def-cohomology`, restricted to `k` along the structure morphism. The homogeneous
polynomial submodule realizes the symmetric power in the ordered homogeneous coordinates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace

/-- Serre's computation, including dimension zero, the canonical sheaf, and the
cohomology of the structure sheaf. All cohomology is computed in module sheaves, and
all displayed cohomology isomorphisms are in `ModuleCat k`.

Source: blueprint main-20261015, sec-picard-framework/sk-thm-picard-pn/_section.md;
Stacks Project, Tag 01XT, lemma-cohomology-projective-space-over-ring, equation-identify;
blueprint lem-pc-projective-space-canonical. (blueprint: sk-thm-picard-pn)

Proof:
1. In dimension zero, projective space is Spec k. Each twist is free of rank one,
so its sections are k and its positive cohomology vanishes, by
lem-pc-projective-space-twist-cohomology. The zeroth exterior power is the structure
sheaf by def-sc-sheaf-exterior-power, giving the canonical-sheaf formula too.
2. For positive dimension the standard opens D_+(x_i) cover and their intersections
are affine (def-pc-proj). The twists are locally free of rank one and quasi-coherent
(def-pc-projective-space-twist). Compute their cohomology by the standard affine Cech
cover (lem-pc-cech-computes), replace it by the ordered complex
(lem-pc-alternating-cech-computes), and split it into its Laurent exponent summands
(lem-pc-twist-cech-monomial-decomposition).
3. By lem-pc-monomial-cech-complex-homology, an exponent with no negative entries
contributes k in degree zero, one with all entries negative contributes k in degree n,
and all others contribute zero. Cycles and boundaries commute with this direct sum:
a finite-support boundary has preimages with finite support. The monomial bases are
k-bases, also supplied by lem-pc-projective-space-twist-cohomology over A = k.
4. Nonnegative exponents of sum m form the monomial basis of the degree-m polynomial
submodule, which is S^m(k^(n+1)). Strictly negative exponents have sum at most -n-1;
thus the top cohomology vanishes for m >= -n when n >= 1.
5. For m <= -n-1 the bijection e -> -e-1 identifies the negative-exponent basis
with the finite monomial basis of degree -m-n-1. Map each Cech class to the dual
coordinate functional. This gives the top-degree k-linear isomorphism.
6. Apply lem-pc-projective-space-canonical over k: its isomorphism sends
(-1)^i wedge_{j != i} d(x_j/x_i) to the standard local generator of O(-n-1).
The exterior sheaf here is exactly the one of def-sc-sheaf-exterior-power.
7. Set m = 0: the only nonnegative exponent vector of sum zero is zero and there
is no strictly negative vector of sum zero. Hence H^0(O) = k and H^q(O) = 0 for q > 0,
also in dimension zero by step 1. -/
theorem picard_pn (k : Type u) [Field k] (n : ℕ) :
    (∀ m : ℤ, 0 ≤ m →
      Nonempty (
        (ModuleCat.restrictScalars
          (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
          ((RingedSpace.moduleCohomology
            ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace 0).obj
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)) ≅
          ModuleCat.of k
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k m.toNat))) ∧
    (∀ (q : ℕ) (m : ℤ), q ≠ 0 → q ≠ n →
      IsZero (
        (ModuleCat.restrictScalars
          (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
          ((RingedSpace.moduleCohomology
            ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace q).obj
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)))) ∧
    (1 ≤ n → ∀ m : ℤ, -(n : ℤ) ≤ m →
      IsZero (
        (ModuleCat.restrictScalars
          (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
          ((RingedSpace.moduleCohomology
            ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace n).obj
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)))) ∧
    (1 ≤ n → ∀ m : ℤ, m ≤ -(n : ℤ) - 1 →
      Nonempty (
        (ModuleCat.restrictScalars
          (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
          ((RingedSpace.moduleCohomology
            ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace n).obj
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)) ≅
          ModuleCat.of k (Module.Dual k
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k
              (-m - n - 1).toNat)))) ∧
    (n = 0 → IsIso (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)) ∧
      ∀ m : ℤ,
        Nonempty (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m ≅
          SheafOfModules.unit ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).ringCatSheaf) ∧
        Nonempty (
          (ModuleCat.restrictScalars
            (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
            ((RingedSpace.moduleCohomology
              ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace 0).obj
              (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)) ≅ ModuleCat.of k k) ∧
        ∀ q : ℕ, q ≠ 0 → IsZero (
          (ModuleCat.restrictScalars
            (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
            ((RingedSpace.moduleCohomology
              ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace q).obj
              (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)))) ∧
    Nonempty (Scheme.Modules.exteriorSheaf
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials n ≅
        twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (-(n : ℤ) - 1)) ∧
    Nonempty (
      (ModuleCat.restrictScalars
        (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
        ((RingedSpace.moduleCohomology
          ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace 0).obj
          (SheafOfModules.unit ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).ringCatSheaf)) ≅
        ModuleCat.of k k) ∧
    (∀ q : ℕ, q ≠ 0 → IsZero (
      (ModuleCat.restrictScalars
        (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
        ((RingedSpace.moduleCohomology
          ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace q).obj
          (SheafOfModules.unit ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).ringCatSheaf)))) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
