/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Paper.PrincipalKoszulStrictReplacement

/-! # Computing integral reduction on an arbitrary representative

Source: the finite-free quotient resolution in paragraph 1 of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 06YY, 08J7, and 07A6.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

/-- The fixed strict Koszul coefficient tower computes the actual reduction tower
on any representative of the resolved derived object.

Source: paragraph 1 of `lem-coef-integral-hom-reduction.proof.md`, and Stacks
Tags 06YY, 08J7, and 07A6 (blueprint: lem-sf-integral-reduction-koszul-model).

Proof: refine q to a flat-term K-flat resolution. Tensor its terms with the
compatible principal Koszul augmentations. Regularity of the completed uniformizer,
divisibility of the projection kernel, and surjectivity of the projection identify
each coefficient augmentation as a quasi-isomorphism. The strict replacement theorem
therefore identifies this tensor tower with termwise scalar extension followed by
restriction. The scalar-extension counit and its pure-tensor normalization identify
its transitions with the actual integralReductionTower transitions. Resolution
independence transports this identification back to q. Each Q_n is bounded with
free terms and hence K-flat. Thus the functor N ↦ (N tensor Q_n)_n sends every
quasi-isomorphism to an objectwise quasi-isomorphism; after localization it factors
through the derived category. Apply that factorization to e to replace G by N.
The strict (a,id) coefficient transitions make all these isomorphisms natural in n.
The exponent n+1 is positive even at n=0; no boundedness of N or flatness of its
terms is used, and the construction also applies to the zero complex and empty site. -/
theorem integralReductionTower_koszul_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P G N : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (e : DerivedCategory.Q.obj N ≅ DerivedCategory.Q.obj G) :
    Nonempty (integralReductionTower l E Y D hl P ≅
      principalKoszulTower (completedIntegralCommRingSheaf l E Y D hl)
        (PrincipalKoszulStrictReplacement.uniformizer l E Y) ⋙
          (totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj N ⋙
            DerivedCategory.Q) := by sorry

end WeilConjectures.IntegralHom
