/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Naturality and involutivity of the recorded rational Koszul symmetry

Source: blueprint lem-coef-rational-retract-evaluation, proof paragraph 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] WeilConjectures.rationalDerivedTensor
  WeilConjectures.pullbackTensorRationalBraiding

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The specified rational signed swap is natural and its opposite swap is inverse.
Source: blueprint lem-coef-rational-retract-evaluation, paragraph 2, and
lem-pur-derived-pullback-tensor-iso's signed total-tensor normalization
(blueprint: lem-coef-rational-tensor-symmetry-laws).

Proof: in the coherent reduction category the swap on degrees r,s sends
x tensor y to (-1)^(r*s) y tensor x. This commutes with both input maps;
the composite of the two swaps is identity since (-1)^(2*r*s)=1.
The tensor/reduction comparisons conjugate these two equations to the
completed integral tensor. Reduction is faithful on the complete inputs,
so the equations hold integrally. The rational tensor and swap are the
specified scalar localizations of these maps. Naturality for pure tensors
is the integral equation multiplied by their two scalars, and extends to
arbitrary arrows by bilinearity. Localizing the integral inverse equation
proves the last identity, including zero objects. -/
theorem rationalTensorSymmetry_laws
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∀ (K L P Q : sfRationalConstructibleCategory l E X) (i : P ⟶ K) (j : Q ⟶ L),
      (@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) Q P).hom ≫
          (RationalVerdier.tensor D l hl X E).map (Prod.mkHom i j) =
      (RationalVerdier.tensor D l hl X E).map (Prod.mkHom j i) ≫
        (@pullbackTensorRationalBraiding l _ E _ _ _ X
          (RationalVerdier.units D l hl X) L K).hom) ∧
    (∀ K L : sfRationalConstructibleCategory l E X,
      (@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) K L).hom ≫
      (@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) L K).hom = 𝟙 _) := by
  sorry

end WeilConjectures
