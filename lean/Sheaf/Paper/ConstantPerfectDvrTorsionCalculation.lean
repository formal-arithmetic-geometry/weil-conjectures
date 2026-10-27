/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T6
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-! # The elementary-divisor and periodic-resolution calculation for one perfect value

Source: the DVR calculation in the proof of the integral truncation criterion;
Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The completed realization of a single perfect valuation-ring complex has free
and nilpotent torsion cohomology, with the positive elementary divisors detected by
consecutive-quotient Tor. There is no constructibility assumption, stratification or
choice of local model in this statement: its input is an actual perfect complex of
modules over the valuation ring. The arbitrary map g just restricts this fixed value.

Source: the elementary-divisor and periodic-resolution steps 2--3 of
lem-weil-pbc-adic-cohomology-torsion-normal-form; Bhatt--Scholze, Lemma 6.5.8 and
Proposition 6.6.11 for realization and restriction.
(blueprint: lem-weil-pbc-constant-perfect-dvr-torsion-calculation).

Proof: represent C by a bounded finite-projective complex. The valuation ring is a
DVR, so all its terms are finite free. Starting at the highest nonzero degree, choose
Smith bases for the image of the preceding differential in that term. Lift an image
basis to the preceding term. Since the image is free, these lifts split off a direct
summand complementary to the differential kernel. The incoming differential lands in
that kernel, so these two-term summands split as complexes. Recurse on the remaining
bounded complex. Normalize each nonzero Smith coefficient to a uniformizer power by
absorbing its unit in a basis vector. Unit blocks are contractible. Thus H^q consists
of a free module A^r and finitely many A/(pi^s) with s positive. Apply completed constant
realization and exact inverse image along g. Finite free realization is the r-fold
power of the pulled completed ring, giving a basis on every object's sections.
Let N be the sum of the positive-power cokernels and f multiplication by pi. The
largest exponent kills N; for no torsion take the zero module and exponent zero.
Choose n at least that largest exponent. At exponent n+2 every degree-q torsion block
still has H^q equal to A/(pi^s). Other blocks may contribute to H^q of the reduction,
but the complex decomposition makes the designated degree-q summands direct summands.
For S=A/(pi^(n+2)) and R=A/(pi^(n+1)), the free periodic resolution of R over S has
first differential pi^(n+1), second differential pi, then alternates. Its kernel and
image identities follow by cancellation in the DVR. Tensoring with A/(pi^s), with
s at most n+1, gives Tor_1 equal to A/(pi^s) modulo pi. On the designated finite sum,
this is exactly cokernel f. Projection from the other summands is an epimorphism.
Constant sheafification is exact, and the bounded-above free resolution computes
ordinary derived extension. Completed constant finite-complex realization compares
all finite reductions with these actual quotient complexes. Exact inverse image
commutes with homology and derived scalar extension. Restrict quotient scalars along
the pulled completion projection to obtain the displayed epimorphism. On an empty
chart its target and source are zero, and the same projection is still epimorphic. -/
theorem pbc_constant_perfect_dvr_torsion_calculation
    (T X : Scheme.{u}) (g : X ⟶ T)
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (C : completedConstantDerived
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)))
    (hC : @DerivedCategory.IsPerfectRingComplex _ _ (HasDerivedCategory.standard _) C)
    (q : ℤ) :
    let d := pbcPadicCoefficientDatum l E
    let B := pbcAdicCompletion T d
    let K := (integralConstantDerived T d).obj C
    let B' := (adicTowerInverseImage g).obj B
    let P := proEtaleRingModulePullback g B B' (Iso.refl _)
    let tor (n : ℕ) := (DerivedCategory.homologyFunctor _ (-1)).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pbcCompletedReduction T d (n + 1)).obj K))))
    ∃ (r : ℕ) (F N : pbcModules X B'),
      (∀ U : X.ProEtᵒᵖ,
        Nonempty (Module.Basis (Fin r) (B'.obj.obj U) (F.val.obj U))) ∧
      Nonempty (P.obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅ F ⊞ N) ∧
      ∃ f : End N, IsNilpotent f ∧ ∃ n : ℕ,
        ∃ t : (pbcRestrict ((adicTowerInverseImage g).map
            (pbcAdicProjection T d n))).obj
          ((proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
            ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n)))
            (Iso.refl _)).obj (tor n)) ⟶ cokernel f,
          Epi t := by sorry

end AlgebraicGeometry.Scheme
