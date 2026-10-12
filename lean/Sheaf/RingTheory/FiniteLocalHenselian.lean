module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.RingTheory.EtaleRetractionFiniteProductLocal
import Sheaf.RingTheory.HenselianEtaleRetraction
import Sheaf.RingTheory.HenselianLocalRootLifting

/-! Henselianity of a module-finite local algebra. -/

@[expose] public section

universe u v

namespace HenselianLocalRing

/-- A module-finite local algebra over a henselian local ring is henselian.
Source: Stacks Project, Algebra, Tag 04GH (lemma-finite-over-henselian), part (2).
(blueprint: lem-weil-pbc-finite-local-henselian)

Proof: let A be the local algebra and let C be any finite A-algebra. It is finite
as an R-module by transitivity. The henselian etale retraction theorem and the
finite-algebra product-local theorem decompose C as a finite product of local
rings C_j. Transport the A-algebra structure to this product. Each projection is
surjective, so each C_j is finite over A. Its maximal ideal pulls back to the
maximal ideal n of A by integrality. Thus n C_j is contained in its maximal ideal,
and C_j / n C_j is a nonzero local ring. Quotienting the product by n C gives
the product of these quotients. An idempotent in a local ring is zero or one,
since e (1-e) = 0 and one of e and 1-e is a unit. Hence every idempotent of
C / n C is a zero-one vector and lifts to the identical vector in the product C.
The lift is unique, again componentwise. The empty product covers C = 0.
The idempotent-lifting/simple-root equivalence now gives HenselianLocalRing A. -/
theorem finite_local_henselian
    (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [HenselianLocalRing R] [IsLocalRing A] [Algebra R A] [Module.Finite R A] :
    HenselianLocalRing A := by
  sorry

end HenselianLocalRing
