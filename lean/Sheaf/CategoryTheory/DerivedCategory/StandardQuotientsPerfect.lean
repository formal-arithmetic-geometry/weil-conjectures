/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Perfectness of the standard coefficient quotients

Source: literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/
lem-weil-pbc-standard-quotients-perfect.md, node order 1254; Stacks Project, Tag 0657
(blueprint: lem-weil-pbc-standard-quotients-perfect).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The standard ℓ-adic and finite-extension quotient modules are represented by the
corresponding two-term finite-free complexes and are finite as sets.

Source: literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/
lem-weil-pbc-standard-quotients-perfect.md, Proof and Source note; Stacks Project, Tag 0657
(blueprint: lem-weil-pbc-standard-quotients-perfect).

Proof plan (the five DAG steps):
1. By `def-weil-l-adic-numbers`, the base ring is a DVR with uniformizer `l` and
   quotient `ZMod (l ^ n)`. For the extension, use the absolute value and chosen
   uniformizer of `def-weil-l-adic-coefficient-extension` and apply
   `lem-weil-l-adic-extension-integers-dvr`. Both coefficient rings are domains,
   their uniformizers are nonzero, and the extension has finite residue field
   (`def-sc-discrete-valuation-ring`).
2. For either pair `(A,t)`, the domain property makes `t ^ n` nonzero, hence
   multiplication by it injective and A-linear. Induction using the ideal product
   of `def-weil-pbc-algebra-hom-quotient` gives `(tA)^n = t^n A`: products of
   generators give one inclusion, and `t^(n+1)c = (t^n c)t` gives the other.
   The surjective quotient map has kernel `t^n A`, the multiplication map's image.
3. Put A in degrees -1 and 0, zero elsewhere, with this multiplication differential.
   The quotient augmentation is a chain map since it kills `t^n A`. Its degree -1
   cohomology is zero by injectivity; its degree-zero cohomology is `A/t^n A`.
   The induced map sends the class of x to its quotient class; its inverse is
   well defined because two representatives differ by `t^n A`. All other
   cohomologies vanish. Thus the augmentation is a quasi-isomorphism and its
   image under Q is invertible (`def-weil-abstract-derived-category`). In the
   base case compose with the indicated quotient identification to `ZMod (l ^ n)`.
4. The two terms have basis 1, so they are finite free. For projectivity, lift a
   map from A through a surjection by lifting the image of 1 and extending
   A-linearly. Zero terms use the empty basis and zero lift. These bounded finite
   projective models give the two perfect objects by `def-pc-perfect-ring-complex`
   and Stacks Tag 0657, with exactly the displayed differentials and augmentations.
5. The base quotient is finite via its `ZMod (l ^ n)` identification. For the
   extension, `lem-weil-valued-dvr-finite-quotients` applies to its DVR, finite
   residue field and uniformizer and makes every positive quotient finite.
   This verifies precisely the ordinary-module perfectness and finite-set
   requirements of `def-weil-pbc-adic-coefficient-datum`, without asserting any
   comparison of completed and constant coefficient sheaf categories.
-/
theorem standard_quotients_perfect
    (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 1 ≤ n) :
    (∃ (e : ZMod (l ^ n) ≃+* PadicInt l ⧸
        (Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n),
      e.symm.toRingHom.comp
          (Ideal.Quotient.mkₐ (PadicInt l)
            ((Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n)).toRingHom =
        PadicInt.toZModPow n ∧
      ∃ (P : CochainComplex (ModuleCat (PadicInt l)) ℤ)
      (hPge : P.IsStrictlyGE (-1)) (hPle : P.IsStrictlyLE 0),
      (∀ i : ℤ, Module.Free (PadicInt l) (P.X i) ∧
        Module.Finite (PadicInt l) (P.X i)) ∧
      DerivedCategory.IsPerfectRingComplex
        ((DerivedCategory.singleFunctor (ModuleCat (PadicInt l)) 0).obj
          ((ModuleCat.restrictScalars (PadicInt.toZModPow n)).obj
            (ModuleCat.of (ZMod (l ^ n)) (ZMod (l ^ n))))) ∧
      ∃ (em : P.X (-1) ≅ ModuleCat.of (PadicInt l) (PadicInt l))
        (e0 : P.X 0 ≅ ModuleCat.of (PadicInt l) (PadicInt l)),
        P.d (-1) 0 = em.hom ≫
          ModuleCat.ofHom
            (LinearMap.mulLeft (PadicInt l) ((l : PadicInt l) ^ n)) ≫ e0.inv ∧
        ∃ (φ : DerivedCategory.Q.obj P ≅
            (DerivedCategory.singleFunctor (ModuleCat (PadicInt l)) 0).obj
              ((ModuleCat.restrictScalars (PadicInt.toZModPow n)).obj
                (ModuleCat.of (ZMod (l ^ n)) (ZMod (l ^ n)))))
          (ε : P ⟶ (CochainComplex.singleFunctor (ModuleCat (PadicInt l)) 0).obj
            ((ModuleCat.restrictScalars (PadicInt.toZModPow n)).obj
              (ModuleCat.of (ZMod (l ^ n)) (ZMod (l ^ n))))),
          DerivedCategory.Q.map ε = φ.hom ∧
          (∀ x : P.X 0, ε.f 0 x =
            e.symm (Ideal.Quotient.mk
              ((Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n)
              (e0.hom x))) ∧
          (∀ i : ℤ, i ≠ 0 → ε.f i = 0) ∧
        Finite (PadicInt l ⧸
          (Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n)) ∧
    (∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E],
      ∃ (P : CochainComplex
          (ModuleCat (Padic.coefficientExtensionIntegers l E)) ℤ)
        (hPge : P.IsStrictlyGE (-1)) (hPle : P.IsStrictlyLE 0),
        (∀ i : ℤ,
          Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
            Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i)) ∧
        DerivedCategory.IsPerfectRingComplex
          ((DerivedCategory.singleFunctor
            (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).obj
            (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionIntegers l E ⧸
                (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set
                  (Padic.coefficientExtensionIntegers l E))) ^ n))) ∧
        ∃ (em : P.X (-1) ≅
            ModuleCat.of (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionIntegers l E))
          (e0 : P.X 0 ≅
            ModuleCat.of (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionIntegers l E)),
          P.d (-1) 0 = em.hom ≫
              ModuleCat.ofHom
                (LinearMap.mulLeft (Padic.coefficientExtensionIntegers l E)
                  ((Padic.coefficientExtensionUniformizer l E) ^ n)) ≫ e0.inv ∧
          ∃ (φ : DerivedCategory.Q.obj P ≅
              (DerivedCategory.singleFunctor
                (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).obj
                (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
                  (Padic.coefficientExtensionIntegers l E ⧸
                    (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set
                      (Padic.coefficientExtensionIntegers l E))) ^ n)))
            (ε : P ⟶ (CochainComplex.singleFunctor
                (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).obj
                (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
                  (Padic.coefficientExtensionIntegers l E ⧸
                    (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set
                      (Padic.coefficientExtensionIntegers l E))) ^ n))),
            DerivedCategory.Q.map ε = φ.hom ∧
            ε.f 0 = e0.hom ≫ ModuleCat.ofHom
              (AlgHom.toLinearMap
                (Ideal.Quotient.mkₐ (Padic.coefficientExtensionIntegers l E)
                  ((Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set
                    (Padic.coefficientExtensionIntegers l E))) ^ n))) ∧
            (∀ i : ℤ, i ≠ 0 → ε.f i = 0) ∧
          Finite (Padic.coefficientExtensionIntegers l E ⧸
            (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set
              (Padic.coefficientExtensionIntegers l E))) ^ n)) := by
  sorry

end AlgebraicGeometry
