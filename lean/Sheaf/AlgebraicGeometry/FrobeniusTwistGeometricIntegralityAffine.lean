/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Over
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Sheaf.AlgebraicGeometry.SchemeCharacteristic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Geometric integrality and affine charts of Frobenius twists

Source: Stacks Project, Varieties, Tags 0CC9 and 0CCG; Schemes, Tags 01I4 and 01JR
(blueprint: lem-sfb-frobenius-twist-geometric-integrality-affine).

The tensor helpers name Mathlib's tensor product with its right scalar structure changed
by the given endomorphism. They contain actual tensor data, including for the zero ring.
The projection identities characterize all the canonical scheme maps uniquely.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The tensor ring with right scalar structure `φ`.
Source: Stacks, Tags 0CCG and 01I4
(blueprint: lem-sfb-frobenius-twist-geometric-integrality-affine). -/
def scalarTwistTensor (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (φ : k →+* k) : CommRingCat.{u} :=
  @CommRingCat.of
    (@TensorProduct k inferInstance A k inferInstance inferInstance
      (Algebra.toModule : Module k A) φ.toAlgebra.toModule)
    (@Algebra.TensorProduct.instCommRing k A k inferInstance inferInstance
      inferInstance inferInstance φ.toAlgebra)

/-- The elementary tensor in the scalar-twisted tensor ring.
Source: Stacks, Tags 0CCG and 01I4
(blueprint: lem-sfb-frobenius-twist-geometric-integrality-affine). -/
def scalarTwistTensorTmul (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (φ : k →+* k) (a : A) (b : k) : scalarTwistTensor k A φ :=
  @TensorProduct.tmul k inferInstance A k inferInstance inferInstance
    (Algebra.toModule : Module k A) φ.toAlgebra.toModule a b

/-- The first tensor inclusion, `a ↦ a ⊗ 1`.
Source: Stacks, Tags 0CCG and 01I4
(blueprint: lem-sfb-frobenius-twist-geometric-integrality-affine). -/
def scalarTwistTensorInl (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (φ : k →+* k) : A →+* scalarTwistTensor k A φ :=
  @Algebra.TensorProduct.includeLeftRingHom k A k inferInstance inferInstance
    inferInstance inferInstance φ.toAlgebra

/-- The second tensor inclusion, giving the scalar structure `b ↦ 1 ⊗ b`.
Source: Stacks, Tags 0CCG and 01I4
(blueprint: lem-sfb-frobenius-twist-geometric-integrality-affine). -/
def scalarTwistTensorInr (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (φ : k →+* k) : k →+* scalarTwistTensor k A φ :=
  @AlgHom.toRingHom k k (scalarTwistTensor k A φ) inferInstance inferInstance
    inferInstance φ.toAlgebra
    (@Algebra.TensorProduct.instAlgebra k A k inferInstance inferInstance
      inferInstance inferInstance φ.toAlgebra)
    (@Algebra.TensorProduct.includeRight k A k inferInstance inferInstance
      inferInstance inferInstance φ.toAlgebra)

/-- Frobenius twists preserve geometric integrality, commute with arbitrary field
extension through the composite scalar map, and have the stated affine tensor charts.
The two projection identities specify relative Frobenius, and the affine ring map is
linear for the second tensor factor, including at the zeroth iterate.

Source: Stacks Project, Varieties, Tags 0CC9 and 0CCG; Schemes, Tags 01I4 and 01JR
(blueprint: lem-sfb-frobenius-twist-geometric-integrality-affine).

Proof:
1. The prime p vanishes in every section ring of X, by pulling back its vanishing in k
   and restricting. Ring homomorphisms preserve p^n-th powers, so absolute Frobenius
   commutes with s. The fibre-product universal property gives the pair map F, with
   first projection the absolute iterate and second projection s.
2. For a field embedding iota, a point of the iterated fibre product is a compatible
   triple (a,b,c). Eliminating b gives the pair (a,c), with scalar map iota composed
   with the p^n-power map. These operations are inverse on projections, hence give
   the canonical isomorphism. Geometric integrality applies to this field embedding;
   equivalently, geometric integrality is preserved by this base change.
3. The open-fibre-product lemma identifies the twisted affine chart with the inverse
   image of the original chart. Such opens cover because the original affine opens
   cover. The affine fibre-product lemma identifies the chart with the displayed
   tensor spectrum and its two tensor inclusions. Since absolute Frobenius is the
   identity on points, F has precisely the asserted inverse images of these opens.
4. The tensor pushout property constructs H by a tensor b ↦ a^(p^n) alpha(b).
   Balancing holds because alpha(c)^(p^n) = alpha(c^(p^n)). Its composites with the
   inclusions are the power map and alpha. Thus Spec H is the restriction of F by
   uniqueness of the pair map. The second inclusion identity gives k-linearity.
5. At n=0 the power maps are identities. The first projection has inverse (id,s)
   by the pullback universal property and identifies F with id. The affine formula
   becomes a tensor b ↦ a alpha(b), inverse to a ↦ a tensor 1 by balancing.
Dependencies: def-weil-ring-frobenius, def-weil-absolute-frobenius-scheme,
 def-pc-fibre-product, def-weil-scheme-characteristic-p, def-weil-affine-spectrum,
 def-pc-geometrically-irreducible, lem-weil-pbc-open-fibre-product,
 lem-weil-pbc-fibre-product-affine-spectra,
 lem-weil-pbc-algebra-tensor-pushout-universal-property. -/
theorem frobeniusTwist_geometricIntegrality_affine
    (k : Type u) [Field k] (p : ℕ) (hp : p.Prime) [CharP k p]
    (X : Scheme.{u}) (s : X ⟶ Spec (.of k)) [GeometricallyIntegral s] (n : ℕ) :
    ∃ hX : (p : Γ(X, ⊤)) = 0,
    ∃ F : X ⟶ pullback s
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n))),
      F ≫ pullback.fst s
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n))) =
          X.iterateFrobenius hp hX n ∧
      F ≫ pullback.snd s
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n))) =
          s ∧
      GeometricallyIntegral (pullback.snd s
        (Spec.map (CommRingCat.ofHom (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n)))) ∧
      (∀ (k' : Type u) [Field k'] (ι : k →+* k'),
        ∃ e : pullback (pullback.snd s
              (Spec.map (CommRingCat.ofHom
                (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n))))
              (Spec.map (CommRingCat.ofHom ι)) ≅
            pullback s (Spec.map (CommRingCat.ofHom
              (ι.comp (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n)))),
          e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ ∧
          e.hom ≫ pullback.snd _ _ = pullback.snd _ _) ∧
      (∀ y : (pullback s
          (Spec.map (CommRingCat.ofHom
            (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n))) : Scheme.{u}),
        ∃ U : X.affineOpens, pullback.fst s
          (Spec.map (CommRingCat.ofHom
            (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n))) y ∈ U.1) ∧
      (∀ (A : Type u) [CommRing A] [Algebra k A]
          (i : Spec (.of A) ⟶ X) [IsOpenImmersion i],
          i ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k A)) →
        ∃ j : Spec (scalarTwistTensor k A
              (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n)) ⟶
            pullback s (Spec.map (CommRingCat.ofHom
              (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n))),
          IsOpenImmersion j ∧
          j ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom
            (scalarTwistTensorInl k A
              (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n))) ≫ i ∧
          j ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
            (scalarTwistTensorInr k A
              (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n))) ∧
          Set.range j = (pullback.fst s
            (Spec.map (CommRingCat.ofHom
              (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n)))) ⁻¹' Set.range i ∧
          F ⁻¹' Set.range j = Set.range i ∧
          ∃ H : scalarTwistTensor k A
              (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n) →+* A,
            H.comp (scalarTwistTensorInr k A
              (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n)) = algebraMap k A ∧
            (∀ (a : A) (b : k), H (scalarTwistTensorTmul k A
              (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n) a b) =
                a ^ (p ^ n) * algebraMap k A b) ∧
            Spec.map (CommRingCat.ofHom H) ≫ j = i ≫ F ∧
            (n = 0 → ∀ (a : A) (b : k), H (scalarTwistTensorTmul k A
              (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n) a b) =
                a * algebraMap k A b)) ∧
      (n = 0 → IsIso (pullback.fst s
          (Spec.map (CommRingCat.ofHom
            (iterateFrobeniusOfPrime k hp (CharP.cast_eq_zero k p) n)))) ∧
        F ≫ pullback.fst _ _ = 𝟙 X) := by
  sorry

end AlgebraicGeometry
