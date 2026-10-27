/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Koszul
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Data.Finset.Powerset
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-! # The exact coordinate Koszul sequence on projective space

Source: Stacks Project, perfect.tex, Tag 0BQS, lemma-construct-the-next-one
(blueprint: lem-sfb-projective-coordinate-koszul-sequence).

The terms are coproducts indexed by subsets of the homogeneous coordinates. The
matrix formula fixes the differential to be exterior multiplication by the sum
of the coordinates, with the ordered-subset signs. An integer-indexed complex
includes both exterior zero terms: there are no subsets of negative cardinality
or cardinality greater than n + 1. The twists and coordinate multiplication maps
are the existing projective-space constructions, with no new choices of maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace

/-- The signed coordinate Koszul sequence of vector bundles on projective n-space
is exact, for every commutative ring and every integer twist.

Source: Stacks Project, perfect.tex, Tag 0BQS, lemma-construct-the-next-one
(blueprint: lem-sfb-projective-coordinate-koszul-sequence).

The coordinate type is the universe lift of Fin (n + 1), as in the shared
projective-space model. In degree i, the subsets of cardinality i label the copies
of O(a+i). In the displayed matrix formula, a contribution from I to J is zero
unless J = insert j I with j outside I; its coefficient is (-1) to the number
of elements of I smaller than j, times multiplication by x_j. The associativity
transport only identifies (a+i)+1 with a+(i+1).

Proof:
1. The standard opens D_+(x_k) cover projective space (def-pc-proj). The twists
   (def-pc-projective-space-twist) have generators e_k^(d) and transition functions
   (x_k/x_l)^d. Coordinate multiplication sends e_k^(d) to (x_j/x_k)e_k^(d+1);
   these maps agree on overlaps, for every integer d. Finite matrices of them
   give the displayed differentials in the abelian module-sheaf category
   (def-weil-sheaf-of-modules-category). The terms are locally free of the ranks
   binomial(n+1,i), with zero terms outside the indicated range.
2. In the square of the differential, the two ways of adjoining distinct j,l
   have opposite signs and the same coefficient x_j x_l. They cancel over any
   commutative ring, including characteristic two, so this is a cochain complex.
3. On D_+(x_k), put t_j=x_j/x_k, so t_k=1. Contract a basis vector indexed by I
   to zero if k is outside I, and otherwise to (-1)^(#{l in I | l<k}) times the
   vector indexed by I minus k. Direct calculation gives delta h + h delta = 1:
   the k term is the identity, and all other terms cancel in pairs. This includes
   the first and last nonzero degrees. The contractions need not glue.
4. A section in the kernel therefore has a preimage on each standard chart.
   Apply lem-weil-pbc-ringed-space-module-exactness-local-lifting to obtain
   exactness at each term. In degree zero the contraction says a kernel section
   restricts to zero on every chart, hence is zero by the sheaf axiom. The exterior
   zero degrees are exact as well. No exactness of global sections is required. -/
theorem exists_exact_coordinateKoszulSequence (A : Type u) [CommRing A]
    (n : ℕ) (a : ℤ) :
    ∃ E : CochainComplex (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))).Modules ℤ,
      ∃ e : ∀ i : ℤ, E.X i ≅
        ∐ fun _ : {I : Finset (ULift.{u} (Fin (n + 1))) // (I.card : ℤ) = i} ↦
          twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) (a + i),
        E.Acyclic ∧ (∀ i : ℤ, (E.X i).IsFiniteLocallyFree) ∧
        ∀ (i : ℤ)
          (I : {I : Finset (ULift.{u} (Fin (n + 1))) // (I.card : ℤ) = i}),
          Sigma.ι
              (fun _ : {I : Finset (ULift.{u} (Fin (n + 1))) // (I.card : ℤ) = i} ↦
                twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) (a + i)) I ≫
              (e i).inv ≫ E.d i (i + 1) ≫ (e (i + 1)).hom =
            ∑ J : {J : Finset (ULift.{u} (Fin (n + 1))) // (J.card : ℤ) = i + 1},
              ∑ j : ULift.{u} (Fin (n + 1)),
                if j ∉ I.val ∧ insert j I.val = J.val then
                  ((-1 : ℤ) ^ (I.val.filter (fun k ↦ k.down < j.down)).card) •
                    (twistMulX (ULift.{u} (Fin (n + 1))) (Spec (.of A)) j (a + i) ≫
                      eqToHom (congrArg
                        (twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)))
                        (add_assoc a i 1)) ≫
                      Sigma.ι
                        (fun _ : {J : Finset (ULift.{u} (Fin (n + 1))) //
                            (J.card : ℤ) = i + 1} ↦
                          twist (ULift.{u} (Fin (n + 1))) (Spec (.of A))
                            (a + (i + 1))) J)
                else 0 := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
