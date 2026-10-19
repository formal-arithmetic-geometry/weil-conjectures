/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import Mathlib.RingTheory.Henselian

/-!
# Character splittings of tame unit extensions

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VI,
proof 3.7(a), printed pp. 74--75 (blueprint: lem-per-tame-unit-extension-character).

The statement records the equivariant extension of a fine saturated sharp lattice by
units of a strictly henselian local ring, together with its root-of-unity character.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A tame unit extension has an equivariant positive section and a root-of-unity
character. Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VI,
proof 3.7(a), printed pp. 74--75 (blueprint: lem-per-tame-unit-extension-character).

Proof (the seven steps of the DAG):
1. For `n = |H|`, the principal units `U = 1 + m` are uniquely `n`-divisible:
   apply `lem-weil-pbc-henselian-local-root-lifting` to `T^n - u` with residue root
   one and `lem-weil-pbc-simple-root-uniqueness` with unit derivative. Uniqueness
   makes the root map `r : U → U` a homomorphism commuting with `H`.
2. Write `z_h(ℓ) = h(s₀(ℓ)) / s₀(ℓ)` in the kernel `Aˣ`. Then
   `z_{gh} = g(z_h) z_g`; trivial residue action makes its reduction a character.
3. Multiplying the residue cocycle identity over `H` and reindexing gives
   `zbar_g(ℓ)^n = 1` by cancellation.
4. Lift these residue roots uniquely through `T^n - 1`, using the same root-lifting
   and uniqueness dependencies. Their lifts `α_h(ℓ)` are multiplicative in both
   variables. Uniqueness also shows every `n`th root of unity is fixed by `H`.
5. Set `d_h = z_h / α_h`, a principal-unit cocycle, and `P(ℓ) = ∏ h, d_h(ℓ)`.
   The cocycle identity and reindexing give `g(P(ℓ)) / P(ℓ) = d_g(ℓ)^(-n)`.
6. Put `b = r ∘ P`. By simple-root uniqueness in `U`, the preceding identity gives
   `g(b(ℓ)) / b(ℓ) = d_g(ℓ)⁻¹`.
7. Set `s(ℓ) = b(ℓ) s₀(ℓ)`. This remains a section since `b` is in the kernel,
   and remains positive since `b` is a monoid unit. Its action cocycle is `α`.
   The resulting bilinear pairing factors through `Abelianization H` and then
   the tensor product with `L`, giving `χ` and the displayed formula.
-/
theorem exists_tame_unit_extension_character
    (A : Type u) [CommRing A]
    [IsStrictlyHenselianLocalRing A]
    (H : Type v) [Group H] [Finite H]
    (ρ : H →* (A ≃+* A))
    (hres : ∀ (h : H) (a : A), IsLocalRing.residue A ((ρ h) a) =
      IsLocalRing.residue A a)
    (M : Type w) [CommMonoid M]
    (unitEquiv : Aˣ ≃* Mˣ)
    (L : Type x) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (Lplus : Submonoid (Multiplicative L))
    (hLfs : IsFineSaturatedMonoid Lplus)
    (hLsharp : ∀ x : Lplus, IsUnit x → x = 1)
    (hLgen : Subgroup.closure (Set.range Lplus.subtype) = ⊤)
    (nunit : IsUnit (Nat.card H : A))
    (eAct : H →* (Algebra.GrothendieckGroup M ≃* Algebra.GrothendieckGroup M))
    (eAct_unit : ∀ (h : H) (a : Aˣ),
      eAct h
          ((Algebra.GrothendieckGroup.of.comp
            (Units.coeHom M)).comp unitEquiv.toMonoidHom a) =
        (Algebra.GrothendieckGroup.of.comp
          (Units.coeHom M)).comp unitEquiv.toMonoidHom
          (Units.map (ρ h).toMonoidHom a))
    (q : Algebra.GrothendieckGroup M →* Multiplicative L)
    (i : Aˣ →* Algebra.GrothendieckGroup M)
    (hi : i = (Algebra.GrothendieckGroup.of.comp
      (Units.coeHom M)).comp unitEquiv.toMonoidHom)
    (hinj : Function.Injective i)
    (hq : ∀ e, q e = 1 ↔ ∃ a, i a = e)
    (hqsurj : Function.Surjective q)
    (s₀ : Multiplicative L →* Algebra.GrothendieckGroup M)
    (hs₀ : q.comp s₀ = MonoidHom.id (Multiplicative L))
    (hqact : ∀ (h : H) (e : Algebra.GrothendieckGroup M),
      q (eAct h e) = q e)
    (hpos : ∀ (x : Lplus), ∃ m : M,
      Algebra.GrothendieckGroup.of m = s₀ x) :
    ∃ (s : Multiplicative L →* Algebra.GrothendieckGroup M)
      (χ : TensorProduct ℤ (Additive (Abelianization H)) L →+
        Additive (rootsOfUnity (Nat.card H) A)),
      q.comp s = MonoidHom.id (Multiplicative L) ∧
      (∀ (x : Lplus), ∃ m : M,
        Algebra.GrothendieckGroup.of m = s x) ∧
      (∀ (h : H) (ℓ : L),
        eAct h (s (Multiplicative.toAdd.symm ℓ)) =
          i ((χ (TensorProduct.tmul ℤ (Additive.ofMul (Abelianization.of h)) ℓ)).toMul) *
            s (Multiplicative.toAdd.symm ℓ)) ∧
      (∀ (h : H) (ζ : rootsOfUnity (Nat.card H) A),
        (ρ h) ((ζ : Aˣ) : A) = ((ζ : Aˣ) : A)) := by
  sorry

end AlgebraicGeometry
