/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.WfTensorUnitSquare.WfTensorUnitSquareData

/-! # Generator-normalized transport of the strict Koszul fiber

Source: the level, product, and mapping-fiber steps of the Frobenius tensor-unit argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.WfTensorUnitSquare
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A) (e : Aut X)

/-- A normalized constant comparison transports the augmented strict Koszul fiber.
Source: blueprint, sec-six-functors/sk-rem-sf-pf-done,
fix-prop-projection-formula.proof.md, penultimate sentence; steps 2 and 3 of
lem-wf-tensor-pullback-completion-unit-square.
(blueprint: lem-wf-normalized-koszul-fiber-unit-transport).

Proof: map the normalized constant comparison degreewise to the finite Koszul
complex. Naturality gives compatibility with its transitions and identifies the
degree-zero inclusion, since it is induced from the rank-one constant generator.
The stipulated pure-tensor formula for ordinary pullback then identifies the image
of z tensor 1 with its target counterpart. Check on each totalization inclusion;
this gives beta_m H(iota_m) = alpha iota'_m. Pullback along the scheme automorphism
preserves countable products. Compose its canonical product comparison with the
beta_m to construct delta. Product projections prove both the displayed
normalization and delta H(u) = alpha u'. Compatibility with the transitions makes
delta intertwine minus one-minus-shift. Functoriality of the shifted mapping cone
then constructs b using delta on its two coordinates. The actual unit is the
zero-homotopy lift (u,0), so these coordinates give the asserted chain-map equality.
No quasi-isomorphism or flatness is used in this calculation. At m=0 the positive
power is p; for p=0 or a unit, and for zero input complexes, the same formulas hold. -/
theorem normalizedKoszulFiber_unit_transport (p : A)
    (k : constants X d ⋙ transport X d e ≅ constants X d)
    (hk : NormalizedConstants X d e k)
    (U V : CochainComplex (adicDatumModules X (intrinsicPresentationDatum d)) ℤ) :
    ∃ (delta : (complexes X d e).obj (product X d p (tensor X d U V)) ≅
        product X d p (tensor X d ((complexes X d e).obj U)
          ((complexes X d e).obj V)))
      (b : (complexes X d e).obj (fiber X d p (tensor X d U V)) ≅
        fiber X d p (tensor X d ((complexes X d e).obj U)
          ((complexes X d e).obj V))),
      NormalizedFiber X d e p k U V delta b ∧
      (complexes X d e).map (unit X d p (tensor X d U V)) ≫ b.hom =
        (alpha X d e U V).hom ≫ unit X d p
          (tensor X d ((complexes X d e).obj U) ((complexes X d e).obj V)) := by sorry

end WeilConjectures.WfTensorUnitSquare
