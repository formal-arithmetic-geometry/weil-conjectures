/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.ProjectiveBundleFormula
public import Sheaf.Paper.KummerAdditivity
public import Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.DirectSum.Module
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
import Sheaf.AlgebraicGeometry.SupportLongExact
import Sheaf.CategoryTheory.ModuleRestrictionKernelComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Geometric projective-space cohomology and the positive hyperplane class

Source: Milne, Lectures on Etale Cohomology, Example 16.3 and the first paragraph of
Theorem 23.2's proof (blueprint: lem-per-geometric-projective-space-hyperplane-cohomology).

The algebra presentation is expressed by homogeneous polynomial evaluation: it is
surjective and its kernel is precisely the multiples of X^(m+1). Evaluation uses the
published ordered derived tensor powers, so its variable is the positive Kummer class.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor
open DirectSum

namespace AlgebraicGeometry.Etale

/-- Global invertibility of the coefficient exponent, used by the Kummer definition.
Source: Milne, Section 16, invertible coefficient exponent
(blueprint: lem-per-geometric-projective-space-hyperplane-cohomology).
Proof: raise the field unit l to the power n. Map it through the inverse of
Gamma(Spec k)=k, then through the global-section map of the projective structure
morphism. Ring homomorphisms preserve units and natural-number casts. -/
theorem geometricProjectiveExponentUnit (k : Type u) [Field k] (l n m : ℕ)
    (hl : IsUnit (l : k)) :
    IsUnit ((l ^ n : ℕ) :
      Γ(ProjectiveSpace (ULift.{u} (Fin (m + 1))) (Spec (.of k)), ⊤)) := by
  sorry

/-- The actual positive Kummer class of O(1), with its ordered cup powers.
Source: Milne, Section 23, codimension-one cycle class and Theorem 23.2
(blueprint: lem-per-geometric-projective-space-hyperplane-cohomology). -/
def geometricProjectiveHyperplanePower (k : Type u) [Field k] (l n m : ℕ)
    (hl : IsUnit (l : k)) (a : ℕ) :=
  WeilConjectures.projectiveBundleCupPowerRaw (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n)
    (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n))
    (ProjectiveSpace (ULift.{u} (Fin (m + 1))) (Spec (.of k)))
    (kummerFirstChern (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n))
      (ProjectiveSpace (ULift.{u} (Fin (m + 1))) (Spec (.of k)))
      (geometricProjectiveExponentUnit k l n m hl)
      (Scheme.Pic.ofIsInvertible
        (ProjectiveSpace.twist (ULift.{u} (Fin (m + 1))) (Spec (.of k)) 1))) a

/-- The diagonal component H^(2a)(P,Lambda(a)), in the existing ordered shifted
Tate-power presentation. Source: Milne, Example 16.3 and Theorem 23.2
(blueprint: lem-per-geometric-projective-space-hyperplane-cohomology). -/
abbrev geometricProjectiveDiagonal (k : Type u) [Field k] (l n m a : ℕ) :=
  ordinaryFiniteUnit (ULift.{u + 1} (ZMod (l ^ n)))
      (ProjectiveSpace (ULift.{u} (Fin (m + 1))) (Spec (.of k))) ⟶
    affineLinearBaseCoefficient (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n)
      (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n))
      (ProjectiveSpace (ULift.{u} (Fin (m + 1))) (Spec (.of k))) a

/-- Geometric projective-space cohomology, including its specified polynomial
presentation. Source: Milne, Example 16.3 and Theorem 23.2, first proof paragraph
(blueprint: lem-per-geometric-projective-space-hyperplane-cohomology).

Proof plan:
1. Use the standard charts to identify D=V(x_m) with P^(m-1), and its complement
   with A^m. The chart equations are nonzerodivisors. The smooth affine charts give
   smoothness of P and D; properness gives finite type and separatedness, and
   finite type over a field gives Noetherianity. Transitions identify O(D)=O(1)
   and its restriction with O_D(1).
2. Apply thm-pur-with-support-exactness and lem-per-smooth-divisor-kummer-purity.
   lem-pur-module-restriction-kernel-comparison identifies the abelian and module
   localization sequences. lem-per-geometric-affine-space-acyclicity then gives
   the Gysin recurrence H^(q-2)(D,Lambda(t-1))=H^q(P,Lambda(t)) for q>=2,
   H^0=Lambda(t)(k), and H^1=0.
3. Induct on m for all integer q,t simultaneously, with P^0=A^0 as base case.
   Negative degrees vanish for a sheaf placed in degree zero. This gives odd and
   above-top vanishing, including q=2m+1.
4. lem-asd-ordinary-supported-kummer normalizes i_*(1)=+h and i^*h=h_D.
   The projection identity of lem-per-noetherian-supported-product-calculus gives
   i_*(h_D^(a-1))=h^a. Thus the specified maps b -> b h^a are isomorphisms.
5. Associativity and bilinearity of that product identify polynomial evaluation
   with the diagonal graded-algebra map. Step 4 gives its surjectivity, while
   vanishing above 2m and injectivity in lower degrees give kernel (X^(m+1)).
   For m=0, h=0 and the algebra is Lambda. No finite-field hypothesis is used.
-/
theorem geometricProjectiveSpaceHyperplaneCohomology (k : Type u) [Field k]
    [IsAlgClosed k] (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 1 ≤ n)
    (hl : IsUnit (l : k)) (m : ℕ) :
    (∀ a : ℕ, a ≤ m → Function.Bijective
      (fun b : ULift.{u + 1} (ZMod (l ^ n)) ↦
        b • geometricProjectiveHyperplanePower k l n m hl a)) ∧
    (∀ q t : ℤ, Odd q ∨ (2 * m : ℤ) < q ∨ q < 0 →
      Subsingleton
        (ordinaryFiniteUnit (ULift.{u + 1} (ZMod (l ^ n)))
            (ProjectiveSpace (ULift.{u} (Fin (m + 1))) (Spec (.of k))) ⟶
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateSheaf (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n)
              (ProjectiveSpace (ULift.{u} (Fin (m + 1))) (Spec (.of k)))
              (CharP.cast_eq_zero (ULift.{u + 1} (ZMod (l ^ n))) (l ^ n)) t))⟦q⟧)) ∧
    (∀ x : (⨁ a : ℕ, geometricProjectiveDiagonal k l n m a),
      ∃ p : Polynomial (ULift.{u + 1} (ZMod (l ^ n))), ∀ a : ℕ,
        x a = p.coeff a • geometricProjectiveHyperplanePower k l n m hl a) ∧
    (∀ p : Polynomial (ULift.{u + 1} (ZMod (l ^ n))),
      (∀ a : ℕ, p.coeff a • geometricProjectiveHyperplanePower k l n m hl a = 0) ↔
        Polynomial.X ^ (m + 1) ∣ p) := by
  sorry

end AlgebraicGeometry.Etale
