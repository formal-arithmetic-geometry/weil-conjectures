/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralLineTensorComparisonDefinitions


/-! Integral line tensor comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t})

/-- A line has a K-flat single complex, its tensor with a good complex is good,
and scalar extension commutes with that total tensor with the specified generators.
Source: Stacks 06YQ, 06YY and 07A4
(blueprint: lem-sf-integral-line-tensor-comparison-representative).

Proof: a rank-one trivialization makes tensor by T the identity on module sheaves.
Exactness is local, so T is flat. Its degree-zero single complex is bounded above
with flat terms, hence K-flat. Tensor of two K-flat complexes is K-flat by the
associativity isomorphism and the acyclic-tensor criterion. Each term of the total
complex is a direct sum of tensors of flat modules and is therefore flat. This
proves that the tensor with P belongs to Good. At each quotient, extend scalars on
the direct-sum total tensor. On the summand in bidegree (p,q), the balanced map is
 a tensor (x tensor y) ↦ (a tensor x) tensor (1 tensor y).
Its inverse sends (a tensor x) tensor (b tensor y) to ab tensor (x tensor y).
The balancing relations make both maps well defined and inverse; sheafification
and the coproduct universal property extend them to all sections and all summands.
The maps commute with the two differential components because scalar extension
is additive, and both total differentials have the same sign (-1)^p in the second
component. They therefore give the asserted chain isomorphism β. Its formula on
sheafified pure tensors is precisely the displayed equation. The argument includes
n = 0, whose quotient is the positive first power, and arbitrary unbounded P. -/
theorem integralLineTensorComparison_representative
    (T : Mod l E X none) [T.IsFiniteLocallyFreeOfRank 1]
    (P : (Good l E X none).FullSubcategory) :
      ∃ (hT : CochainComplex.IsKFlatIndependentCoefficients
          (J := topology X none) (R := ring l E X none)
          ((integralLineSingle l E X).obj T))
        (hS : Good l E X none (integralLineComplex l E X P.obj T)),
        ∀ n : ℕ, ∃ β :
            (integralLineFiniteComplex l E X n).obj (integralLineComplex l E X P.obj T) ≅
              integralLineFiniteTensor l E X P.obj T n,
          (∀ (p q k : ℤ) (hpq : p + q = k) (V : X.ProEtᵒᵖ)
              (a : (finite l E X none n).obj.obj V)
              (x : (P.obj.X p).val.obj V)
              (y : (((integralLineSingle l E X).obj T).X q).val.obj V),
            (β.hom.f k).val.app V
                (generator l E X none n ((integralLineComplex l E X P.obj T).X k) V a
                  (coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                    (ring l E X none) P.obj ((integralLineSingle l E X).obj T)
                    p q k hpq V x y)) =
              coefficientTensorGenerator.{u, t + 1, t} (topology X none)
                (finite l E X none n) ((integralLineFiniteComplex l E X n).obj P.obj)
                ((integralLineFiniteComplex l E X n).obj ((integralLineSingle l E X).obj T))
                p q k hpq V (generator l E X none n (P.obj.X p) V a x)
                (generator l E X none n (((integralLineSingle l E X).obj T).X q) V 1 y)) := by
  sorry

end WeilConjectures
