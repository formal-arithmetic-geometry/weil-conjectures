module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Canonical quotients of marked Artinian tests

Source: Stacks Project, Formal Deformation Theory, Tag 06SZ,
lemma-largest-closed-where-lift (blueprint: def-sfb-artin-test-quotient).

The underlying algebra is the literal ideal quotient. Its augmentation is induced
by the given test arrow and the target's residue marking.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k] [Algebra R k]
  [Algebra.FiniteType R k]

/-- The canonical algebra map from the literal quotient to the target.
Source: Stacks, Tag 06SZ (blueprint: def-sfb-artin-test-quotient). -/
def quotientToAlgebra {B A : TestCategory R k} (f : B ⟶ A)
    (L : Ideal (ring B)) (hL : L ≤ RingHom.ker (map f).toRingHom) :
    (ring B ⧸ L) →ₐ[R] ring A :=
  Ideal.Quotient.liftₐ L (map f) (fun _ hb ↦ hL hb)

/-- The quotient's marked augmentation, induced by the target's marking.
Source: Stacks, Tag 06SZ (blueprint: def-sfb-artin-test-quotient). -/
def testQuotientResidue {B A : TestCategory R k} (f : B ⟶ A)
    (L : Ideal (ring B)) (hL : L ≤ RingHom.ker (map f).toRingHom) :
    (ring B ⧸ L) →ₐ[R] k :=
  (residue A).comp (quotientToAlgebra f L hL)

/-- The literal quotient, with the induced marking, is a test algebra.
Source: Stacks, Tag 06SZ (blueprint: def-sfb-artin-test-quotient).
Proof: the test arrow preserves residues, so its kernel is contained in the maximal
ideal of B. Thus L is proper, and B/L is local. Descending chains of its ideals
correspond to chains of ideals of B containing L, so it is Artinian. Its residue
augmentation is induced by that of B, hence is surjective and has kernel the
maximal ideal of B/L. These are exactly the four fields of IsTestAlgebra. -/
theorem testQuotient_isTestAlgebra {B A : TestCategory R k} (f : B ⟶ A)
    (L : Ideal (ring B)) (hL : L ≤ RingHom.ker (map f).toRingHom) :
    IsTestAlgebra R k (A := CommAlgCat.of R (ring B ⧸ L))
      (testQuotientResidue f L hL) := sorry

/-- The literal quotient B/L as a marked test algebra.
Source: Stacks, Tag 06SZ (blueprint: def-sfb-artin-test-quotient). -/
def testQuotient {B A : TestCategory R k} (f : B ⟶ A)
    (L : Ideal (ring B)) (hL : L ≤ RingHom.ker (map f).toRingHom) : TestCategory R k :=
  ⟨Over.mk (CommAlgCat.ofHom (testQuotientResidue f L hL)),
    testQuotient_isTestAlgebra f L hL⟩

/-- The canonical marked test arrow B/L to A, sending the class of b to f(b).
Source: Stacks, Tag 06SZ (blueprint: def-sfb-artin-test-quotient). -/
def testQuotientTo {B A : TestCategory R k} (f : B ⟶ A)
    (L : Ideal (ring B)) (hL : L ≤ RingHom.ker (map f).toRingHom) :
    testQuotient f L hL ⟶ A :=
  ObjectProperty.homMk
    (Over.homMk (CommAlgCat.ofHom (quotientToAlgebra f L hL)) rfl)

end AlgebraicGeometry.ArtinDeformation
