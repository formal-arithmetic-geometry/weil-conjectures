module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! Factorization data for a generalized inverse.

This is the algebraic splitting output of the universal rank-one kernel argument.
The existence of the factorization is the local matrix and projectivity argument
from Stacks Project, Tags 00O0 and 00NX.
(blueprint: new-universal-h0-split-factorization)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

/-- The local algebra argument supplies a split factorization of the first
 differential through an intermediate projective direct summand.

The proof is the local matrix and projective-cokernel argument of Stacks
Project, Tags 00O0 and 00NX: localize at primes, reduce the finite projective
map to an identity block and a zero block using the rank-one residue-kernel
hypothesis, then use finite presentation and local freeness to obtain a
projective cokernel. Splitting the quotient and the induced surjection onto
the image yields the displayed maps and identities.
(blueprint: new-universal-h0-split-factorization) -/
theorem universalH0_split_factorization
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hf0 : Module.Finite R (P.X 0))
    (hf1 : Module.Finite R (P.X 1))
    (hp0 : Module.Projective R (P.X 0))
    (hp1 : Module.Projective R (P.X 1))
    (hneg : IsZero (P.X (-1)))
    (hzero : ∀ (B : Type v) [CommRing B] (φ : R →+* B),
      let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
      Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) :
    ∃ (I : ModuleCat.{v} R) (e : P.X 0 ⟶ I) (p : I ⟶ P.X 1)
      (r : I ⟶ P.X 0) (q : P.X 1 ⟶ I),
      P.d 0 1 = e ≫ p ∧ e ≫ r = 𝟙 (P.X 0) ∧ p ≫ q = 𝟙 I := by sorry

end CochainComplex
