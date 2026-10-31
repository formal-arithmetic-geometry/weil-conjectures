/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Etale.StandardEtale

/-! # Prime-power cyclotomic transition and root-splitting charts

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md`, Proof (1), primitive-root schemes
(blueprint: lem-pur-cyclotomic-tower-charts).

The abbreviations only specialize the existing localization, polynomial and quotient
constructions. All chart maps below are specified on every polynomial representative.
The successor algebra structure is quantified with its defining coefficient map, so the
statement can use the genuine algebra equivalence and tensor product APIs without choosing
a transition map before asserting its existence.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped Polynomial TensorProduct
open AlgebraicGeometry CategoryTheory Polynomial

namespace CyclotomicTowerCharts

universe u

/-- The base Z[1/ell]. Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev base (ell : ℕ) : Type := Localization.Away (ell : ℤ)

/-- The integer cyclotomic polynomial with coefficients localized in the base.
Source: primitive-root schemes, Proof (1) (blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev polynomial (ell n : ℕ) : (base ell)[X] :=
  (Polynomial.cyclotomic (ell ^ n) ℤ).map (algebraMap ℤ (base ell))

/-- C_n = Z[1/ell][T]/(Phi_(ell^n)). Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev ring (ell n : ℕ) : Type := AdjoinRoot (polynomial ell n)

/-- The class z_n of T. Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev root (ell n : ℕ) : ring ell n := AdjoinRoot.root (polynomial ell n)

/-- The transition presentation polynomial Y^ell-z_n. Source: primitive-root schemes,
Proof (1) (blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev stepPolynomial (ell n : ℕ) : (ring ell n)[X] := X ^ ell - C (root ell n)

/-- The splitting polynomial Y^(ell^n)-1. Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev rootsPolynomial (ell n : ℕ) : (ring ell n)[X] := X ^ (ell ^ n) - 1

/-- The finite etale cyclotomic covers, their power transitions, and the transition and
root-splitting charts, including all commutative-algebra base changes.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md`, Proof (1), primitive-root schemes
(blueprint: lem-pur-cyclotomic-tower-charts).

Proof plan (the seven steps of the node):
1. The cyclotomic power identity gives z_n^(ell^n)=1. Differentiating it shows that
   Phi'(z_n)(z_n^(ell^(n-1))-1)=(ell^n)z_n^(ell^n-1), a unit, hence Phi'(z_n) is a unit.
2. Monicity and positive degree give a finite free quotient and injective coefficient map
   (lem-weil-pbc-monic-quotient-free). Finite-algebra integrality and lying over
   (lem-weil-pbc-finite-algebra-is-integral, lem-weil-pbc-integral-injective-lying-over)
   give a finite surjection. Inverting the already invertible derivative identifies the
   quotient with a standard etale algebra (lem-weil-pbc-standard-etale-monic-derivative).
3. Phi_(ell^n)(T^ell)=Phi_(ell^(n+1))(T) gives the transition map. The maps between
   C_n[Y]/(Y^ell-z_n) and C_(n+1) fix coefficients and the displayed generator in both
   composites (lem-pur-cyclotomic-power-identity, def-weil-pbc-algebra-hom-quotient).
4. The transition polynomial is monic with unit derivative ell*y^(ell-1). Apply the same
   finite-free, integral, lying-over and standard-etale arguments as in step 2.
5. The geometric sum for w=z_n^(ell^(n-1)) shows ell is a multiple of 1-w. For
   0<k<ell^n write k=ell^s*u with ell not dividing u, and choose v inverse to u modulo
   ell^(n-s). The geometric sums show 1-w is a multiple of 1-z_n^(ell^s), in turn a
   multiple of 1-z_n^k. Thus 1-z_n^k and all differences of distinct root powers are units.
6. Apply lem-pur-monic-unit-difference-evaluation to Y^(ell^n)-1 over the nonzero C_n,
   with roots z_n^a, indexed by their residue classes. This gives exactly evaluation.
7. Under coefficient base change the transition substitutions remain mutually inverse.
   For the splitting chart, root equations and unit differences persist; apply the same
   evaluation lemma when the algebra is nonzero. For the zero algebra all the displayed
   quotients, tensor products and finite products are zero rings and the maps are unique.
-/
theorem cyclotomicTowerCharts (ell n : ℕ) (hell : ell.Prime) (hn : 1 ≤ n) :
    (IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (base ell) (ring ell n)))) ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap (base ell) (ring ell n)))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap (base ell) (ring ell n))))) ∧
    (∃ e : AdjoinRoot (rootsPolynomial ell n) ≃ₐ[ring ell n]
        (ZMod (ell ^ n) → ring ell n),
      ∀ (p : (ring ell n)[X]) (a : ZMod (ell ^ n)),
        e (AdjoinRoot.mk (rootsPolynomial ell n) p) a = p.eval (root ell n ^ a.val)) ∧
    (∀ (A : Type u) [CommRing A] [Algebra (ring ell n) A],
      ∃ e : AdjoinRoot ((rootsPolynomial ell n).map (algebraMap (ring ell n) A)) ≃ₐ[A]
          (ZMod (ell ^ n) → A),
        ∀ (p : A[X]) (a : ZMod (ell ^ n)),
          e (AdjoinRoot.mk _ p) a = p.eval (algebraMap (ring ell n) A (root ell n) ^ a.val)) ∧
    (∃ t : ring ell n →ₐ[base ell] ring ell (n + 1),
      t (root ell n) = root ell (n + 1) ^ ell ∧
      IsFinite (Spec.map (CommRingCat.ofHom t.toRingHom)) ∧
      Etale (Spec.map (CommRingCat.ofHom t.toRingHom)) ∧
      Surjective (Spec.map (CommRingCat.ofHom t.toRingHom)) ∧
      ∀ [nextAlgebra : Algebra (ring ell n) (ring ell (n + 1))],
        (∀ c : ring ell n, algebraMap (ring ell n) (ring ell (n + 1)) c = t c) →
        (∃ e : AdjoinRoot (stepPolynomial ell n) ≃ₐ[ring ell n] ring ell (n + 1),
          ∀ p : (ring ell n)[X],
            e (AdjoinRoot.mk _ p) = p.eval₂ t.toRingHom (root ell (n + 1))) ∧
        (∀ (A : Type u) [CommRing A] [Algebra (ring ell n) A],
          ∃ e : AdjoinRoot ((stepPolynomial ell n).map (algebraMap (ring ell n) A)) ≃ₐ[A]
              A ⊗[ring ell n] ring ell (n + 1),
            ∀ p : A[X], e (AdjoinRoot.mk _ p) =
              p.eval₂ (algebraMap A (A ⊗[ring ell n] ring ell (n + 1)))
                (1 ⊗ₜ[ring ell n] root ell (n + 1)))) := by
  sorry

end CyclotomicTowerCharts
