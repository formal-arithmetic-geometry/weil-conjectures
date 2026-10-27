/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Algebra.Homology.TwoTermFreeHomTensorComponents

/-! # A signed complex representative of integral Hom reduction

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2;
Stacks Tags 093M, 06YQ, 08J7 and 07A6.
(blueprint: lem-sf-integral-hom-comparison-representative).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

-- Use the existing sheafification at the coefficient universe for this declaration.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The restricted comparison has the signed Hom--tensor complex representative.
This asserts its chain-level formula and the normalization square, with no
invertibility assertion about the representative map or its components.

Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraphs 1--2,
finite-free quotient resolution and the evaluation-normalized scalar adjunction;
Stacks Tags 093M, 06YQ, 08J7 and 07A6.
(blueprint: lem-sf-integral-hom-comparison-representative).

Proof: the valuation ring of E is a DVR and is Noetherian. Its standard
resolution of the quotient at exponent n+1 is the free rank-one complex in
degrees -1,0 with differential multiplication by a uniformizer to power n+1.
The completed-constant-sheaf reduction comparison base changes this resolution
to the completed ring sheaf R. It gives Q with the stated support and unit
terms. Bounded-above flat complexes are K-flat, so Q is K-flat. Choose a K-flat
representative P of K and a K-injective representative I of L. Tensoring I
with Q remains K-injective by the bounded split-free tensor lemma. The
localization tensor comparisons identify restricted reduction of Hom(K,L)
with Q applied to Hom(P,I) tensor Q. Scalar adjunction, tested on all slices,
identifies restricted finite Hom with Hom_R(K,Res(F L)), and hence with Q
applied to Hom(P,I tensor Q). These are s and t. On homogeneous tensors define
f(v tensor z)(x)=(-1)^(degree(z)*degree(x)) v(x) tensor z. The three differential
terms involving d_I,d_P,d_Q have signs bp,a+1+bp,a+bp+p on both sides, so f is
a chain map. Evaluation normalization in a and m and the scalar unit
x maps to 1 tensor x identify its localized map with the specified comparison.
Transposing the two candidate maps gives the same reduced evaluation; injectivity
of the target adjunction proves the displayed square. No finiteness of P or I
is used. In particular zero inputs, the empty scheme and n=0 are included. -/
theorem comparison_representative
    (a : TensorPresentation.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))
    (n : ℕ) (m : ReductionPresentation l E Y D hl a n)
    (K L : completedIntegralDerivedCategory l E Y D hl) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    let U := scalarReductionDerivedRestriction l E Y n
    let F := integralDerivedReduction l E Y D hl n
    ∃ (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
      (_ : flat.{t, u} Y R P) (_ : I.IsKInjective)
      (_ : Nonempty (DerivedCategory.Q.obj P ≅ K))
      (_ : Nonempty (DerivedCategory.Q.obj I ≅ L))
      (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
      (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
      (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
        ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
      (f : ((totalTensor.{t, u} Y R).obj
          (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
        homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
          (((totalTensor.{t, u} Y R).obj I).obj Q)),
      IsSignedHomTensor.{t, u} Y R P I Q f ∧
      ∃ (s : U.obj (F.obj ((hom.{t, u} Y R).obj (op K, L))) ≅
          DerivedCategory.Q.obj (((totalTensor.{t, u} Y R).obj
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q))
        (t : U.obj ((hom.{t, u} Y (integralCoefficientCommRingSheaf l E Y n)).obj
            (op (F.obj K), F.obj L)) ≅
          DerivedCategory.Q.obj
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
              (((totalTensor.{t, u} Y R).obj I).obj Q))),
        U.map (comparison l E Y D hl m K L) ≫ t.hom = s.hom ≫ DerivedCategory.Q.map f := by
  sorry

end WeilConjectures.IntegralHom
