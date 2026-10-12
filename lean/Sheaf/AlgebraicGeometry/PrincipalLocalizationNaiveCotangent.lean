/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.LocalizationAway
import Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension

/-!
# Principal localization and the naive cotangent complex

Source: Stacks Project, Algebra, Lemma 08JZ, statement and proof
(blueprint: lem-weil-pbc-principal-localization-naive-cotangent).
-/

@[expose] public section

universe u v w z

open TensorProduct MvPolynomial

namespace Algebra.Generators

/-- A polynomial presentation and its principal localization have the displayed conormal
and differential splittings. Source: Stacks Project, Algebra, Lemma 08JZ
(blueprint: lem-weil-pbc-principal-localization-naive-cotangent).

`P` bundles the surjection alpha from `A[x_s]` and a chosen section; its kernel is `P.ker`.
`localizationAway Bg g` sends its sole variable to `1/g`; its `comp P` is beta.
Its ring `A[x_s,x]` is the usual flattening of `P[x]`. Mathlib writes tensors with the
scalar extension on the left. Thus the degree-zero base change is
`Bg ⊗[B] (B ⊗[P.Ring] Ω[P.Ring⁄A])`, canonically `Bg ⊗[P.Ring] Ω[P.Ring⁄A]`.
The equivalences `e1`, `e2` give clauses (1), (2) with their specified generators;
`e0` and the commuting-square equation give the isomorphism of two-term complexes.

Proof for stage 3, following the node's eight steps:
1. Apply lem-weil-pbc-polynomial-coefficient-map-kernel to alpha on coefficients and
lem-weil-pbc-localization-away-polynomial-quotient to `B[x] → Bg`. Their composite is beta
by def-weil-pbc-mv-polynomial-ring. Both are surjective. Lift a multiplier of `gx-1`
through the first map to show its inverse image is `I P[x] + (fx-1)`.
2. Use lem-weil-pbc-kahler-differentials-polynomial-extension and tensor associativity:
the differential module splits into the old differentials and the free generator `dx`.
3. Inclusion of kernels induces the conormal map; extend its scalars to Bg. Step 1 shows
this image and the class of `fx-1` generate the new conormal module.
4. This inclusion after localization is injective by
lem-weil-pbc-principal-localization-conormal-injective. Its proof maps to `(P/I²)[1/f]`,
where the image of J is square-zero, so a class killed by J² vanishes after localization.
5. By def-weil-pbc-kahler-differentials, the differential on an old class is its old
differential. Leibniz gives `d(fx-1) = g⁻¹ df + g dx`; its dx-coordinate is g.
6. If an old class plus `b[fx-1]` vanishes, apply the dx-coordinate of its differential:
`bg = 0`. Since g is a unit, b = 0; then step 4 kills the old class. Together with
step 3 this proves clause (1), including its rank-one generator.
7. Replace dx by `g⁻² df + dx`. This change of basis fixes the old summand and sends
the differential of `[fx-1]` to g times the new generator. Hence the two equivalences
commute with the differential, proving clause (3).
8. Multiplication by g is bijective. Kernels and cokernels of a direct sum of maps are
the direct sums of their kernels and cokernels. The extra summand therefore has zero
kernel and cokernel, giving the injectivity equivalence and cokernel isomorphism. -/
theorem principal_localization_naive_cotangent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {S : Type w} (P : Generators A B S) (g : B) (f : P.Ring)
    (hf : algebraMap P.Ring B f = g)
    {Bg : Type z} [CommRing Bg] [Algebra B Bg] [Algebra A Bg]
    [IsScalarTower A B Bg] [IsLocalization.Away g Bg] :
    Function.Surjective (aeval (R := A) ((localizationAway Bg g).comp P).val) ∧
    ((localizationAway Bg g).comp P).ker =
      Ideal.map ((localizationAway Bg g).toComp P).toAlgHom.toRingHom P.ker ⊔
      Ideal.span {rename Sum.inr f * X (Sum.inl ()) - 1} ∧
    ∃ (r : ((localizationAway Bg g).comp P).ker),
      r.val = rename Sum.inr f * X (Sum.inl ()) - 1 ∧
      ∃ (e1 : ((localizationAway Bg g).comp P).toExtension.Cotangent ≃ₗ[Bg]
          (Bg ⊗[B] P.toExtension.Cotangent) × Bg)
        (e2 : ((localizationAway Bg g).comp P).toExtension.CotangentSpace ≃ₗ[Bg]
          (Bg ⊗[B] P.toExtension.CotangentSpace) × Bg)
        (e0 : ((localizationAway Bg g).comp P).toExtension.CotangentSpace ≃ₗ[Bg]
          (Bg ⊗[B] P.toExtension.CotangentSpace) × Bg),
        (∀ a b, e1.symm (a, b) =
          LinearMap.liftBaseChange Bg
            (Extension.Cotangent.map ((localizationAway Bg g).toComp P).toExtensionHom) a +
          b • Extension.Cotangent.mk r) ∧
        (∀ a b, e2.symm (a, b) =
          LinearMap.liftBaseChange Bg
            (Extension.CotangentSpace.map ((localizationAway Bg g).toComp P).toExtensionHom) a +
          b • ((1 : Bg) ⊗ₜ[((localizationAway Bg g).comp P).toExtension.Ring]
            KaehlerDifferential.D A ((localizationAway Bg g).comp P).toExtension.Ring
              (X (Sum.inl ())))) ∧
        (∀ a, e0.symm (a, 0) =
          LinearMap.liftBaseChange Bg
            (Extension.CotangentSpace.map ((localizationAway Bg g).toComp P).toExtensionHom) a) ∧
        (∀ a b, ((localizationAway Bg g).comp P).toExtension.cotangentComplex (e1.symm (a, b)) =
          e0.symm (P.toExtension.cotangentComplex.baseChange Bg a,
            algebraMap B Bg g * b)) ∧
        (Function.Injective (P.toExtension.cotangentComplex.baseChange Bg) ↔
          Function.Injective ((localizationAway Bg g).comp P).toExtension.cotangentComplex) ∧
        Nonempty (((Bg ⊗[B] P.toExtension.CotangentSpace) ⧸
            LinearMap.range (P.toExtension.cotangentComplex.baseChange Bg)) ≃ₗ[Bg]
          (((localizationAway Bg g).comp P).toExtension.CotangentSpace ⧸
            LinearMap.range ((localizationAway Bg g).comp P).toExtension.cotangentComplex)) := by
  sorry

end Algebra.Generators
