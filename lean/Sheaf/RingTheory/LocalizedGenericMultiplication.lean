module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Universal injectivity of localized generic multiplication

Source: Stacks Project, Tag 0573, proof of
`lemma-scheme-theoretically-dense-generic-fibre`, third paragraph; Tag 00HL
(blueprint: lem-trf-localized-generic-multiplication-universal-injectivity).
-/

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct

namespace Algebra

universe u v w x y

/-- Multiplication by a finite tuple, as in Stacks Tag 0573, third proof paragraph
(blueprint: lem-trf-localized-generic-multiplication-universal-injectivity). -/
noncomputable def genericMultiplicationTuple (A : Type u) {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] {m : ℕ} (g : Fin m → B) :
    B →ₗ[A] (Fin m → B) :=
  LinearMap.pi fun i => LinearMap.mulLeft A (g i)

/-- The actual cokernel of the tuple map in Stacks Tag 0573. Its range is a
`B`-submodule, so this also gives its cokernel as an `A`-module by restriction.
(blueprint: lem-trf-localized-generic-multiplication-universal-injectivity). -/
abbrev genericMultiplicationCokernel {B : Type v} [CommRing B] {m : ℕ}
    (g : Fin m → B) :=
  (Fin m → B) ⧸ LinearMap.range (genericMultiplicationTuple B g)

/-- The specified localized quotient map in Stacks Tag 0573: on the `i`th
coordinate it sends `b/s` to the class of the `i`th standard vector times `b`,
divided by `s`. Summing the coordinates gives `q_a`, including the empty tuple.
(blueprint: lem-trf-localized-generic-multiplication-universal-injectivity). -/
noncomputable def genericMultiplicationLocalizedQuotient (A : Type u) {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] {m : ℕ} (g : Fin m → B) (a : A) :
    (Fin m → Localization.Away (algebraMap A B a)) →ₗ[A]
      LocalizedModule.Away (algebraMap A B a) (genericMultiplicationCokernel g) :=
  (∑ i : Fin m,
    (IsLocalizedModule.map (Submonoid.powers (algebraMap A B a))
      (Algebra.linearMap B (Localization.Away (algebraMap A B a)))
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A B a))
        (genericMultiplicationCokernel g))
      ((LinearMap.range (genericMultiplicationTuple B g)).mkQ.comp
        (LinearMap.single B (fun _ : Fin m => B) i))).comp
      (LinearMap.proj i)).restrictScalars A

/-- The canonical map `B_a → B ⊗[A] K`, constructed by the localization
universal property, with no choice of an arbitrary comparison map.
Source: Stacks Tag 0573, third proof paragraph.
(blueprint: lem-trf-localized-generic-multiplication-universal-injectivity). -/
noncomputable def genericMultiplicationToFractionTensor (A : Type u) (B : Type v)
    (K : Type w) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K] (a : A) (ha : a ≠ 0) :
    Localization.Away (algebraMap A B a) →ₐ[A] B ⊗[A] K :=
  IsLocalization.Away.liftAlgHom (algebraMap A B a)
    ((congrArg IsUnit
      (((Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).commutes a).trans
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] K).commutes a).symm)).mp
      ((isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr ha)).map
        (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K)))

/-- Localized generic multiplication is universally injective after flattening.
Source: Stacks Tag 0573, third proof paragraph, and Tag 00HL.
(blueprint: lem-trf-localized-generic-multiplication-universal-injectivity).

Proof plan:
1. Localize the cokernel sequence, using `lem-weil-pbc-localization-module-exact`.
   Localization commutes with the finite product by taking common denominators;
   its quotient arrow is precisely `genericMultiplicationLocalizedQuotient`.
2. Flatness of `B_a` and `lem-trf-flat-tensor-preserves-injection` applied to
   `A → K` embed `B_a` in `B_a ⊗ K`. Identify the latter with `B ⊗ K` by
   `(b/a^n) ⊗ k ↦ b ⊗ a^(-n) k`, whose inverse is `b ⊗ k ↦ (b/1) ⊗ k`.
3. The tuple maps commute with this embedding coordinatewise. Their generic
   injectivity therefore gives injectivity of the localized map. Combine with
   step 1 to get the specified short exact sequence, also when `m = 0`.
4. Apply `lem-weil-pbc-flat-quotient-tensor-injective`, since the localized
   cokernel is flat, to obtain injectivity after tensoring with every module.
5. For an algebra `C` inverting `a`, identify `B_a ⊗ C` with `B ⊗ C` by
   `(b/a^n) ⊗ c ↦ b ⊗ (image(a))^(-n)c`. Its inverse sends `b ⊗ c` to
   `(b/1) ⊗ c`. Tensor symmetry and `lem-weil-pbc-tensor-finite-product` identify
   the map in step 4 with multiplication by the tuple `(g_i ⊗ 1)`.
-/
theorem localized_genericMultiplication_universally_injective
    (A : Type u) (B : Type v) (K : Type w)
    [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (m : ℕ) (g : Fin m → B)
    (hgeneric : Function.Injective (genericMultiplicationTuple A
      (fun i => g i ⊗ₜ[A] (1 : K))))
    (a : A) (ha : a ≠ 0)
    [Module.Flat A (Localization.Away (algebraMap A B a))]
    [Module.Flat A
      (LocalizedModule.Away (algebraMap A B a) (genericMultiplicationCokernel g))] :
    Function.Injective (genericMultiplicationToFractionTensor A B K a ha) ∧
    Function.Injective (genericMultiplicationTuple A
      (fun i => algebraMap B (Localization.Away (algebraMap A B a)) (g i))) ∧
    Function.Exact (genericMultiplicationTuple A
      (fun i => algebraMap B (Localization.Away (algebraMap A B a)) (g i)))
      (genericMultiplicationLocalizedQuotient A g a) ∧
    Function.Surjective (genericMultiplicationLocalizedQuotient A g a) ∧
    (∀ (N : Type (max u v w x)) [AddCommGroup N] [Module A N],
      Function.Injective ((genericMultiplicationTuple A
        (fun i => algebraMap B (Localization.Away (algebraMap A B a)) (g i))).lTensor N)) ∧
    (∀ (C : Type (max u v w y)) [CommRing C] [Algebra A C],
      IsUnit (algebraMap A C a) →
      Function.Injective (genericMultiplicationTuple A (fun i => g i ⊗ₜ[A] (1 : C)))) := by
  sorry

end Algebra
