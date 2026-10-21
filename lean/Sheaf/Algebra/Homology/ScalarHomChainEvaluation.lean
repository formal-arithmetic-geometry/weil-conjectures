/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.Algebra.Homology.StrictScalarHomChain

/-! # Scalar evaluation on actual product Hom complexes

Source: Stacks Project, sites-modules.tex, Tags 03CY and 03CZ;
sites-cohomology.tex, Section 0A8X (section-hom-complexes).
(blueprint: lem-sfb-scalar-hom-chain-evaluation).

We reuse the existing normalized tensor, extension, and local evaluation definitions.
The assertion here concerns alpha and sigma and their input naturality only.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u
open CategoryTheory Opposite

namespace SheafOfModules.StrictScalarHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}]

/-- Scalar evaluation and input naturality for the unbounded product Hom complex.
Source: Stacks 03CY (lemma-sheafification-presheaf-modules), 03CZ
(lemma-adjointness-tensor-restrict), and 0A8X (section-hom-complexes).
(blueprint: lem-sfb-scalar-hom-chain-evaluation).

Proof plan, following the ten steps of the node:
1. On each slice define alpha's coordinate by `p ↦ s ⊗ f(p)`. This is linear
in p and balanced bilinear in s and f; restrictions commute with this rule.
2. Extend by the module tensor universal property and then by module sheafification
(def-weil-pbc-module-tensor-product, def-weil-presheaf-modules-sheafification).
3. On each coordinate the signed differential gives
`s ⊗ d_J f(p) - (-1)^n s ⊗ f(d_P p) = s ⊗ (d_H f)(p)`, proving the chain equation
(def-pur-hom-complex, def-pur-sheaf-tensor-product).
4. The unit x ↦ 1 ⊗ x defines a chain map eta. Postcompose the Hom complex
with Uq eta to obtain the R-linear family f ↦ (p ↦ q(1 ⊗ f(p))).
5. Apply the inverse normalized slice scalar-Hom chain adjunction
(lem-sfb-slice-scalar-hom-chain-adjunction) to get beta, whose coordinates send
`t ⊗ p` to `t q(1 ⊗ f(p))`.
6. Extend `(s,f) ↦ s beta(f)` through the tensor and S-module sheafification.
This gives sigma and its displayed formula, on every slice.
7. Since beta is a chain map and the Hom differential is S-linear,
`d sigma(s ⊗ f) = s beta(d f) = sigma(s ⊗ d f)`.
8. For uniqueness, the slice adjunction detects each inner map on `1 ⊗ p`;
product projections detect Hom sections, and tensor generation followed by the
sheafification adjunction detects the outer map. Pure tensors need not exhaust
sections of the sheafified tensor.
9. Alpha's naturality follows because both sides evaluate to
`s ⊗ v(f(u(p)))` on every coordinate over every further slice object.
10. Sigma's two naturality composites evaluate to `st w q(1 ⊗ f(u(p)))`
and `st q'(1 ⊗ v(f(u(p))))`; these agree by `Ev ≫ q' = q ≫ w`.
Use the same three equality tests as in step 8. No boundedness, flatness,
projectivity, K-injectivity, or preservation of infinite products enters. -/
theorem exists_scalarHomChainEvaluation
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    ∃ E : Extension.{c, v, u} φ,
    ∃ α : ∀ (P A : Complex.{c, v, u} R),
      (tensor.{c, v, u} φ).obj (homComplex (R := R) P A) ⟶
        homComplex (R := R) P ((tensor.{c, v, u} φ).obj A),
    ∃ σ : ∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
      (_q : E.complex.obj A ⟶ N),
      E.complex.obj (homComplex (R := R) P A) ⟶
        homComplex (R := S) (E.complex.obj P) N,
    (∀ (P A : Complex.{c, v, u} R) (n i k : ℤ) (h : i + n = k)
      (V : Cᵒᵖ) (s : S.obj.obj V)
      (f : ((homComplex (R := R) P A).X n).val.obj V) (x : (P.X i).val.obj V),
      evaluate.{c, v, u} P ((tensor.{c, v, u} φ).obj A) n i k h V
          (((α P A).f n).val.app V
            (tensorSection.{c, v, u} φ (homComplex (R := R) P A) n V s f)) x =
        tensorSection.{c, v, u} φ A k V s (evaluate.{c, v, u} P A n i k h V f x)) ∧
    (∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
      (q : E.complex.obj A ⟶ N),
      SigmaFormula.{c, v, u} E P A N q (σ P A N q)) ∧
    (∀ (P A : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
      (q : E.complex.obj A ⟶ N)
      (τ : E.complex.obj (homComplex (R := R) P A) ⟶
        homComplex (R := S) (E.complex.obj P) N),
      SigmaFormula.{c, v, u} E P A N q τ → τ = σ P A N q) ∧
    (∀ (P P' A A' : Complex.{c, v, u} R) (a : P' ⟶ P) (b : A ⟶ A'),
      α P A ≫ homMap.{c, v, u} a ((tensor.{c, v, u} φ).map b) =
        (tensor.{c, v, u} φ).map (homMap.{c, v, u} a b) ≫ α P' A') ∧
    (∀ (P P' A A' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
      (q : E.complex.obj A ⟶ N) (q' : E.complex.obj A' ⟶ N')
      (a : P' ⟶ P) (b : A ⟶ A') (w : N ⟶ N'),
      E.complex.map b ≫ q' = q ≫ w →
        σ P A N q ≫ homMap.{c, v, u} (E.complex.map a) w =
          E.complex.map (homMap.{c, v, u} a b) ≫ σ P' A' N' q') := by
  sorry

end SheafOfModules.StrictScalarHom
