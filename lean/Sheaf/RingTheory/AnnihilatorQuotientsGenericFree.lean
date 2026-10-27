module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Exact.Basic
import Sheaf.RingTheory.ReducedPolynomialModuleGenericFreeness
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Simultaneous generic freeness of annihilator and principal quotients

Source: Stacks Project, More on Morphisms, Tag 0575, proof of
`lemma-nonreduced-in-neighbourhood`; Algebra, Tag 051Z
(blueprint: lem-trf-annihilator-quotients-generic-free).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Annihilator and principal quotients become simultaneously free on a principal open.
The ideals `I` and `J` name respectively the annihilator of `b` and the principal ideal `(b)`.
The displayed equations specify all maps canonically, including the quotient identifications.
Localizing each quotient ring at the image of the powers of `g` supplies its usual
`Localization.Away g`-module structure.

Source: Stacks Project, More on Morphisms, Tag 0575,
`lemma-nonreduced-in-neighbourhood`, annihilator argument; Algebra, Tag 051Z
(blueprint: lem-trf-annihilator-quotients-generic-free).

Proof:
1. The images of a finite algebra generating family generate both quotients
(`def-weil-pbc-finite-type-algebra`). Multiplication by `b` descends modulo its
annihilator, is injective, and has image `(b)`, the kernel of the quotient onto `B/J`.
2. If `(B/I)_a` vanished for a nonzero `a`, the fraction criterion would give
`a^r b = 0`. In the zero-prime localization `a` is a unit, contradicting the nonzero
generic image of `b` (`def-weil-pbc-module-localization-away`,
`def-weil-module-base-change`, `def-weil-pbc-localization-at-prime`).
3. Present `B` as a quotient of a polynomial ring in finitely many variables. Both
quotients are cyclic modules over that polynomial ring. A domain is reduced, so
`lem-sfb-reduced-polynomial-module-generic-freeness` applies to each. The dense good
opens are nonempty since the spectrum contains the zero prime. Choose nonzero
principal-open parameters `u` and `v` where the two modules are free
(`def-weil-pbc-mv-polynomial-ring`, `def-weil-finitely-generated-module`,
`def-weil-affine-spectrum`).
4. Put `g = u*v`. Localization of each basis gives a basis after inverting `g`:
expand numerators for spanning, and clear denominators in each finite relation
for independence. No finiteness of either basis is used
(`def-weil-ring-localization-away`, `def-weil-pbc-free-module`). Step 2 gives
nonvanishing of the localized annihilator quotient.
5. On fractions the maps are `(x+I)/g^n ↦ bx/g^n` and
`x/g^n ↦ (x+J)/g^n`. The zero criterion proves injection and identifies the
kernel of the latter with the image of the former; the latter is surjective.
6. The surjections from `B_g` to the two localized quotients have kernels
`Ann(b/1)` and `(b/1)`, respectively: clear a power of `g` in the numerator.
The induced ring equivalences give the canonical identifications. The first
identification intertwines the injection with multiplication by `b/1`.
-/
theorem annihilator_quotients_generic_free
    (A : Type u) [CommRing A] [IsDomain A]
    (B : Type v) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (b : B)
    (hb : TensorProduct.tmul A (1 : Localization.AtPrime (⊥ : Ideal A)) b ≠ 0)
    (I J : Ideal B) (hI : I = (Ideal.span ({b} : Set B)).annihilator)
    (hJ : J = Ideal.span ({b} : Set B)) :
    Algebra.FiniteType A (B ⧸ I) ∧
    Algebra.FiniteType A (B ⧸ J) ∧
    (∃ i : (B ⧸ I) →ₗ[A] B,
      (∀ x : B, i (Ideal.Quotient.mk I x) = b * x) ∧
      Function.Injective i ∧
      Function.Exact i (Ideal.Quotient.mkₐ A J).toLinearMap ∧
      Function.Surjective (Ideal.Quotient.mkₐ A J) ∧
      (∀ a : A, a ≠ 0 →
        Nontrivial (Localization (Algebra.algebraMapSubmonoid (B ⧸ I) (Submonoid.powers a)))) ∧
      ∃ g : A, g ≠ 0 ∧
        Module.Free (Localization.Away g) (Localization (Algebra.algebraMapSubmonoid (B ⧸ I)
          (Submonoid.powers g))) ∧
        Module.Free (Localization.Away g) (Localization (Algebra.algebraMapSubmonoid (B ⧸ J)
          (Submonoid.powers g))) ∧
        Nontrivial (Localization (Algebra.algebraMapSubmonoid (B ⧸ I) (Submonoid.powers g))) ∧
        ∃ (ig : (Localization (Algebra.algebraMapSubmonoid (B ⧸ I) (Submonoid.powers g)))
          →ₗ[Localization.Away g] (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers
          g))))
          (qg : (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g)))
            →ₐ[Localization.Away g] (Localization (Algebra.algebraMapSubmonoid (B ⧸ J)
            (Submonoid.powers g))))
          (c : ((Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))) ⧸ ((Ideal.span
            ({(algebraMap B (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g)))
            b)} : Set (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers
            g))))).annihilator)) ≃ₐ[Localization.Away g] (Localization
            (Algebra.algebraMapSubmonoid (B ⧸ I) (Submonoid.powers g))))
          (d : ((Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))) ⧸ (Ideal.span
            ({(algebraMap B (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g)))
            b)} : Set (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))))))
            ≃ₐ[Localization.Away g] (Localization (Algebra.algebraMapSubmonoid (B ⧸ J)
            (Submonoid.powers g)))),
          (∀ x : B ⧸ I,
            ig (algebraMap (B ⧸ I) (Localization (Algebra.algebraMapSubmonoid (B ⧸ I)
              (Submonoid.powers g))) x) = algebraMap B (Localization (Algebra.algebraMapSubmonoid
              B (Submonoid.powers g))) (i x)) ∧
          (∀ x : B,
            qg (algebraMap B (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g)))
              x) =
              algebraMap (B ⧸ J) (Localization (Algebra.algebraMapSubmonoid (B ⧸ J)
                (Submonoid.powers g))) (Ideal.Quotient.mk J x)) ∧
          Function.Injective ig ∧ Function.Exact ig qg ∧ Function.Surjective qg ∧
          (∀ x : B,
            c (Ideal.Quotient.mk ((Ideal.span ({(algebraMap B (Localization
              (Algebra.algebraMapSubmonoid B (Submonoid.powers g))) b)} : Set (Localization
              (Algebra.algebraMapSubmonoid B (Submonoid.powers g))))).annihilator) (algebraMap B
              (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))) x)) =
              algebraMap (B ⧸ I) (Localization (Algebra.algebraMapSubmonoid (B ⧸ I)
                (Submonoid.powers g))) (Ideal.Quotient.mk I x)) ∧
          (∀ x : Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g)),
            d (Ideal.Quotient.mk (Ideal.span ({(algebraMap B (Localization
              (Algebra.algebraMapSubmonoid B (Submonoid.powers g))) b)} : Set (Localization
              (Algebra.algebraMapSubmonoid B (Submonoid.powers g))))) x) = qg x) ∧
          (∀ x : Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g)),
            ig (c (Ideal.Quotient.mk ((Ideal.span ({(algebraMap B (Localization
              (Algebra.algebraMapSubmonoid B (Submonoid.powers g))) b)} : Set (Localization
              (Algebra.algebraMapSubmonoid B (Submonoid.powers g))))).annihilator) x)) =
              (algebraMap B (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))) b)
              * x)) := by
  sorry

end Algebra
