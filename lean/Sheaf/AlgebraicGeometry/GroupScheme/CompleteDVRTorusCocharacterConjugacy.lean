module

public import Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Integral conjugacy of cocharacters into a split maximal torus

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto decompositions,
Remark 3.5, p.5 (blueprint: lem-sfb-complete-dvr-torus-cocharacter-conjugacy).

Geometric fibres are tested over every algebraically closed field receiving a ring map
from A. Conjugation is expressed in the group of morphisms from the multiplicative group,
so the equality is an equality of scheme morphisms, hence holds on every algebra's points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Over a complete DVR, every cocharacter is integrally conjugate into the prescribed
split maximal torus. No assumption is made on the residue field.

Source: AHLH, Remark 3.5, p.5
(blueprint: lem-sfb-complete-dvr-torus-cocharacter-conjugacy).

Proof plan:
1. Reduce modulo pi. Smoothness persists by lem-pc-proper-base-change. The geometric
   reductivity and maximality hypotheses give a reductive residue-field group and a
   maximal split torus. Apply lem-sfb-field-split-torus-rational-containment to obtain
   a residue-field conjugating point c_1 and a torus cocharacter nu_1.
2. Each coordinate of nu_1 is a group-like Laurent polynomial. Coefficient comparison
   gives orthogonal idempotent coefficients whose sum is one; over a field precisely
   one is one. Thus its coordinates are integer powers of z. The same integer powers
   in the specified splitting define a cocharacter nu over A lifting nu_1.
3. On H use the action t*x = nu(t)*x*lambda(t)^(-1). The group laws verify the action
   identity; its universally fixed points are exactly the desired conjugating points.
   The point c_1 is fixed modulo pi.
4. Inductively lift the particular fixed point c_n modulo pi^n to c_(n+1) modulo
   pi^(n+1), by lem-sfb-gm-fixed-square-zero-lifting. The kernel has square zero
   since 2*n >= n+1 for n >= 1. The lifts are compatible by construction.
5. Write H = Spec C. The compatible maps C -> A/(pi^n) give a map into the inverse
   limit by componentwise operations. Completeness identifies this limit with A,
   yielding c in H(A); separatedness gives the intersection of the powers of pi is zero.
6. The two morphisms G_m -> H agree modulo every pi^n. Every coefficient of the
   difference of the pullbacks of a function in C lies in all powers of pi, so vanishes.
   The affine-spectrum correspondence proves the asserted morphism equality, including
   its interpretation on all algebra points. Rank zero and the trivial cocharacter
   are included throughout. -/
theorem completeDVR_torus_cocharacter_conjugacy
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A))
    [IsAdicComplete (Ideal.span ({π} : Set A)) A]
    (H S : Grp (Over (Spec (.of A))))
    [Smooth H.X.hom] [IsAffine H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (i : S ⟶ H) [IsClosedImmersion i.hom.hom.left]
    (r : ℕ) (e : S ≅ RingGroupSchemes.splitTorus A r)
    (hred : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : A →+* Ω),
      ReductiveTorusCentralizer.IsReductive
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj H))
    (hmax : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : A →+* Ω),
      ReductiveTorusCentralizer.IsMaximalTorus
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map i))
    (mu : RingGroupSchemes.multiplicative A ⟶ H) :
    ∃ (c : 𝟙_ (Over (Spec (.of A))) ⟶ H.X)
      (ν : RingGroupSchemes.multiplicative A ⟶ S),
      (toUnit (RingGroupSchemes.multiplicative A).X ≫ c) * mu.hom.hom *
        (toUnit (RingGroupSchemes.multiplicative A).X ≫ c)⁻¹ =
          ν.hom.hom ≫ i.hom.hom := by
  sorry

end AlgebraicGeometry
