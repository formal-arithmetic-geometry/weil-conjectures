/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.Paper.CompletedTensorHomTranspose
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.SixFunctors.CoefIntegralFiniteExtension
import Sheaf.Paper.IntegralOperationsScalarExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Scalar extension of rational pairing transposes

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-rational-retract-evaluation, proof paragraph 2
(blueprint: lem-coef-rational-scalar-transpose-compatibility).

The helpers only name the specified coefficient extension, the evaluation equation
characterizing an adjoint, and the transported pairing. All duality presentations
and comparison maps retain their recorded integral normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.RationalScalarTranspose

/-- Scalar extension along the actual inclusion of finite fields in the fixed closure.
Source: blueprint retract-evaluation proof paragraph 2
(blueprint: lem-coef-rational-scalar-transpose-compatibility). -/
abbrev extend (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : Scheme.{u}) (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F) :=
  RationalVerdier.scalar C.l X E.val F.val (IntermediateField.inclusion h)

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F)

/-- The pairing whose first adjoint is a: move the second argument to the left by
signed symmetry and then apply the specified argument-first evaluation. The
completed tensor-Hom bijection makes equality to this map exactly the transpose
condition, including for arbitrary rationalized arrows.
Source: blueprint retract-evaluation proof paragraph 2
(blueprint: lem-coef-rational-scalar-transpose-compatibility). -/
def adjointPairing
    (w : IntegralFiniteExtension.DualizingDatum C.l X D C.different E.val)
    (A : RationalVerdier.Datum D C.l C.different X E.val w)
    {K L : sfRationalConstructibleCategory C.l E.val X} (a : K ⟶ A.dual.obj (op L)) :
    (RationalVerdier.tensor D C.l C.different X E.val).obj (K, L) ⟶
      (sfRationalConstructibleLocalization C.l E.val X).obj w.omega :=
  (@pullbackTensorRationalBraiding C.l _ E.val _ _ _ X
      (RationalVerdier.units D C.l C.different X) K L).hom ≫
    (RationalVerdier.tensor D C.l C.different X E.val).map (Prod.mkHom (𝟙 L) a) ≫
      A.evaluation L

/-- The actual extended pairing c_{K,L} followed by T(b) followed by u. The inverse
of rationalTensorScalarComparison has precisely the direction c in the node.
Source: blueprint retract-evaluation proof paragraph 2
(blueprint: lem-coef-rational-scalar-transpose-compatibility). -/
def scalarPairing
    (wE : IntegralFiniteExtension.DualizingDatum C.l X D C.different E.val)
    (wF : IntegralFiniteExtension.DualizingDatum C.l X D C.different F.val)
    (A : RationalVerdier.Datum D C.l C.different X E.val wE)
    (B : RationalVerdier.Datum D C.l C.different X F.val wF)
    (e : RationalVerdier.Extension D C.l C.different X E.val F.val
      (IntermediateField.inclusion h) wE wF A B)
    {K L : sfRationalConstructibleCategory C.l E.val X}
    (b : (RationalVerdier.tensor D C.l C.different X E.val).obj (K, L) ⟶
      (sfRationalConstructibleLocalization C.l E.val X).obj wE.omega) :
    (RationalVerdier.tensor D C.l C.different X F.val).obj
      ((extend D C X E F h).obj K, (extend D C X E F h).obj L) ⟶
      (sfRationalConstructibleLocalization C.l F.val X).obj wF.omega :=
  (@rationalTensorScalarComparison C.l _ E.val _ _ _ F.val _ _ _
      (IntermediateField.inclusion h) X (RationalVerdier.units D C.l C.different X)).inv.app
      (K, L) ≫ (extend D C X E F h).map b ≫ e.omega.hom

/-- Finite scalar extension transports both transposes and the specified restricted
maps and candidate inverse formulas. The hypotheses ha,hc and haF,hcF say exactly
that the four arrows are the transposes under the evaluation bijections, over E
and F respectively. The presentations and ExtensionProperties specify the
canonical dualities, u and beta of rational Verdier duality; they do not replace
these by arbitrary comparisons.
Source: blueprint retract-evaluation proof paragraph 2
(blueprint: lem-coef-rational-scalar-transpose-compatibility).

Proof (the six DAG steps):
1. thm-coef-rational-verdier and lem-coef-integral-finite-extension give the
rationalized canonical evaluation square and contravariant naturality of beta,
for every rational arrow, not only integral representatives.
2. lem-pur-integral-operations-scalar-extension and
 def-weil-derived-pullback-tensor-hom give tensor comparison naturality.
On homogeneous tensors of degrees r,s, both paths through symmetry send
(x tensor lambda) tensor (y tensor mu) to
(-1)^(r*s) (y tensor x) tensor (lambda*mu). Coefficients have degree zero.
The finite quotient maps commute with this calculation, so completion and
rationalization retain it; def-pc-tensor-complex-sheaves fixes the signs.
3. Write b as evaluation after a tensor 1. The evaluation square and tensor
naturality make its extended value evaluation after beta_L T(a) tensor 1.
Injectivity of lem-coef-completed-tensor-hom-transpose gives the first equality.
4. Apply the same calculation to b precomposed with signed symmetry. Step 2
identifies its extension with the swap of b_F, yielding the other equality.
5. T preserves the two split retractions. Naturality at j, composed with T(i)
and T(a), gives the restricted formula. Naturality at i gives its swapped form.
No restricted map has been inverted.
6. Naturality at q, followed by cancellation of beta_L and beta_Q, gives
T(D_E(q)) beta_Q inverse = beta_L inverse D_F(T(q)). Apply functoriality to
p a inverse D_E(q). This is the first candidate-inverse equation. Naturality
at p gives the second equation for c. T(a inverse) beta_L inverse is indeed
the inverse of beta_L T(a), by cancellation and functoriality, and likewise
for c. Nothing asserts invertibility of a restricted transpose. -/
theorem rationalScalarTransposeCompatibility
    (wE : IntegralFiniteExtension.DualizingDatum C.l X D C.different E.val)
    (wF : IntegralFiniteExtension.DualizingDatum C.l X D C.different F.val)
    (A : RationalVerdier.Datum D C.l C.different X E.val wE)
    (B : RationalVerdier.Datum D C.l C.different X F.val wF)
    (e : RationalVerdier.Extension D C.l C.different X E.val F.val
      (IntermediateField.inclusion h) wE wF A B)
    (_he : RationalVerdier.ExtensionProperties D C.l C.different X E.val F.val
      (IntermediateField.inclusion h) wE wF A B e)
    (K L : sfRationalConstructibleCategory C.l E.val X)
    (b : (RationalVerdier.tensor D C.l C.different X E.val).obj (K, L) ⟶
      (sfRationalConstructibleLocalization C.l E.val X).obj wE.omega)
    (a : K ⟶ A.dual.obj (op L)) (c : L ⟶ A.dual.obj (op K))
    (_ha : adjointPairing D C X E wE A a = b)
    (_hc : adjointPairing D C X E wE A c =
      (@pullbackTensorRationalBraiding C.l _ E.val _ _ _ X
        (RationalVerdier.units D C.l C.different X) L K).hom ≫ b)
    (aF : (extend D C X E F h).obj K ⟶ B.dual.obj (op ((extend D C X E F h).obj L)))
    (cF : (extend D C X E F h).obj L ⟶ B.dual.obj (op ((extend D C X E F h).obj K)))
    (_haF : adjointPairing D C X F wF B aF = scalarPairing D C X E F h wE wF A B e b)
    (_hcF : adjointPairing D C X F wF B cF =
      (@pullbackTensorRationalBraiding C.l _ F.val _ _ _ X
        (RationalVerdier.units D C.l C.different X)
        ((extend D C X E F h).obj L) ((extend D C X E F h).obj K)).hom ≫
        scalarPairing D C X E F h wE wF A B e b) :
    aF = (extend D C X E F h).map a ≫ e.comparison.hom.app (op L) ∧
    cF = (extend D C X E F h).map c ≫ e.comparison.hom.app (op K) ∧
    ∀ (P Q : sfRationalConstructibleCategory C.l E.val X)
      (i : P ⟶ K) (p : K ⟶ P) (j : Q ⟶ L) (q : L ⟶ Q),
      i ≫ p = 𝟙 P → j ≫ q = 𝟙 Q →
      ((extend D C X E F h).map (i ≫ a ≫ A.dual.map j.op) ≫
          e.comparison.hom.app (op Q) =
        (extend D C X E F h).map i ≫ aF ≫
          B.dual.map ((extend D C X E F h).map j).op) ∧
      ((extend D C X E F h).map (j ≫ c ≫ A.dual.map i.op) ≫
          e.comparison.hom.app (op P) =
        (extend D C X E F h).map j ≫ cF ≫
          B.dual.map ((extend D C X E F h).map i).op) ∧
      (∀ [IsIso a],
        e.comparison.inv.app (op Q) ≫
            (extend D C X E F h).map (A.dual.map q.op ≫ inv a ≫ p) =
          B.dual.map ((extend D C X E F h).map q).op ≫
            e.comparison.inv.app (op L) ≫ (extend D C X E F h).map (inv a) ≫
              (extend D C X E F h).map p) ∧
      (∀ [IsIso c],
        e.comparison.inv.app (op P) ≫
            (extend D C X E F h).map (A.dual.map p.op ≫ inv c ≫ q) =
          B.dual.map ((extend D C X E F h).map p).op ≫
            e.comparison.inv.app (op K) ≫ (extend D C X E F h).map (inv c) ≫
              (extend D C X E F h).map q) := by
  sorry

end WeilConjectures.RationalScalarTranspose
