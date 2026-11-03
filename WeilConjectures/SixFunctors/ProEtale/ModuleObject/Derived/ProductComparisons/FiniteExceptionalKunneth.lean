/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps

/-! # Exceptional Künneth for arbitrary finite coefficients

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
prop-trf-exceptional-kunneth.md and its proof; Wei Yang #1441, item 27
(blueprint: prop-trf-exceptional-kunneth).

The map is the published exceptional transpose of Ku followed by the two counits.
The coefficient ring is any finite commutative ell-primary ring, with discrete topology.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons

open CompactificationReindexing RelativeKunneth

/-- The specified exceptional comparison is invertible and natural in both inputs.
The localizing adjunctions are the constructible exceptional admissibility data;
no right adjoint on the entire ambient derived category is assumed.
Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/
prop-trf-exceptional-kunneth.proof.md, all six proof paragraphs
(blueprint: prop-trf-exceptional-kunneth).

The purity input is thm-pur-affine-line-purity; generation is
lem-trf-devissage-generation, both for general finite A. The remaining inputs are
sk-lem-sf-kunneth-star, sk-prop-sf-open-closed-triangle, sk-thm-sf-ctf-stability,
lem-sf-etale-shriek-equals-pullback and lem-sf-triangle-two-out-of-three.

Proof: use the canonical Ku isomorphism on the two exceptional images and compose
with both counits; its transpose is alpha. For constants factor affine-space
projections into affine lines. Normalized affine-line purity and its counit
compatibility identify alpha with the twist/shift isomorphism, including dimension
zero. Localization and identity-factor ordinary Künneth give the closed-immersion
case, one variable at a time. Affine closed/smooth factorizations yield the local
case; counit transposition gives agreement on overlaps. Additivity handles finite
free constants. For lisse flat inputs use etale exceptional restriction and
composition to identify the restricted map with alpha on trivializing covers.
The resulting finite projective stalks are retracts of finite free modules; pass
to their summands, then descend invertibility along the etale covers.
Induct on the sum of support dimensions, with zero inputs immediate. Stability
keeps the operations in Dctf and exactness gives triangle two-out-of-three.
For a closed support, exceptional exchange with closed direct image and ordinary
Künneth identify alpha with the closed direct image of the smaller comparison:
both transposes are Ku followed by the same counits. General finite-ring
generation reduces to closed extensions of j_!F with F lisse flat on a dense
stratum. Remove the closed extension by that comparison. Compare j_!F first to
Rj_*F. Exceptional exchange and ordinary Künneth identify the Rj_*-pair with
the direct image of the lisse comparison. The cones of j_!F to Rj_*F are Dctf
on a strictly smaller boundary. Induction and two-out-of-three, first in the
second variable and then the first, give the j_!-pair. Shifts, cones and retracts
extend the result to all inputs. Naturality follows from Ku, the two counits and
the adjunction Hom bijection. Purity and generation hold for arbitrary finite A
by Wei Yang #1441: extend geometric data from Z/ell^N and verify the P1 adjunction
on A-inputs directly; never restrict an A-perfect input to Z/ell^N.
-/
theorem finiteExceptionalKunneth
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hne : ringChar D.k ≠ ell)
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0) :
    let Λ : ScalarSixRing.{u} := ⟨Profinite.continuousMapRingObj A⟩
    let hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X :=
      Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, hA, ⟨Iso.refl _⟩⟩
    let R := relativeDatum D ell hne
    let H := (RelativeKunneth.finiteFieldParameters D ell hne).coefficients Λ hΛ
    let T := R.product Λ hΛ
    ∀ (G : Geometry D.k) (c : Models G)
      (S₁ : SixOperationsLocalizingAdjunction Λ.X c.f₁)
      (S₂ : SixOperationsLocalizingAdjunction Λ.X c.f₂)
      (S : SixOperationsLocalizingAdjunction Λ.X c.relative.total),
      (∀ (L₁ : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
        (L₂ : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left),
        IsIso (alpha Λ H T G c S₁ S₂ S L₁ L₂)) ∧
      (∀ (L₁ L₁' : ConstantModelConstructibleFiniteTor Λ.X G.Y₁.obj.left)
        (L₂ L₂' : ConstantModelConstructibleFiniteTor Λ.X G.Y₂.obj.left)
        (a : L₁ ⟶ L₁') (b : L₂ ⟶ L₂'),
        ((P Λ.X G.r₁.hom.left).map ((exceptional Λ S₁).map a).hom ⊗ₘ
          (P Λ.X G.r₂.hom.left).map ((exceptional Λ S₂).map b).hom) ≫
            (alpha Λ H T G c S₁ S₂ S L₁' L₂').hom =
          (alpha Λ H T G c S₁ S₂ S L₁ L₂).hom ≫
            ((exceptional Λ S).map
              ⟨(P Λ.X G.t₁.hom.left).map a.hom ⊗ₘ
                (P Λ.X G.t₂.hom.left).map b.hom⟩).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
