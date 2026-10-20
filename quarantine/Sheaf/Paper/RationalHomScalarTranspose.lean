/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.Paper.CompletedTensorHomTranspose
public import Sheaf.Paper.SitePerfectComplex

/-! # Canonical rational evaluation comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] WeilConjectures.rationalDerivedTensor
  WeilConjectures.rationalDerivedInternalHom WeilConjectures.podRationalClosed
  WeilConjectures.rationalHomScalarComparison

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finite coefficient passage preserves Hom-first transposition and signed symmetry.
The internal-Hom comparison is the fixed rationalization of the completed one.
Source: blueprint lem-coef-rational-retract-evaluation, proof paragraph 2;
lem-coef-rational-scalar-transpose-compatibility, steps 1--4
(blueprint: lem-coef-rational-hom-scalar-transpose).

Proof: the completed integral Hom comparison is defined by transposing scalar
extension of evaluation. Tensor naturality and the counit identity therefore
identify its composite with the image of every integral transpose. The canonical
completion comparison preserves this identity. Tensor-localize the identity;
both maps are additive and scalar linear, so pure tensors give the equation for
all rational morphisms. For the second equation, on homogeneous representatives
of degrees r,s both paths send (x tensor a) tensor (y tensor b) to
(-1)^(r*s) (y tensor x) tensor (a*b). The fixed quotient comparisons and both
Roos coordinates preserve this equality, as does scalar localization. Nothing
in either calculation requires W to be dualizing, and coefficient embeddings
need not be literal inclusions: the same balanced tensor calculation applies. -/
theorem rationalHomScalar_transpose
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) :
    (∀ (K L W : sfRationalConstructibleCategory l E X)
      (hL : constructibleRationalHomPairs l E X (op L, W))
      (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W),
      (@podRationalClosed l _ F _ _ _ X (RationalVerdier.units D l hl X)).transpose
          ((RationalVerdier.scalar l X E F ι).obj K)
          (rationalHomScalarPair l E F ι X ⟨(op L, W), hL⟩)
          ((@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
            (RationalVerdier.units D l hl X)).inv.app (K, L) ≫
              (RationalVerdier.scalar l X E F ι).map b) =
        (RationalVerdier.scalar l X E F ι).map
          ((@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).transpose
            K ⟨(op L, W), hL⟩ b) ≫
          (rationalHomScalarComparison l E F ι X ⟨(op L, W), hL⟩).hom) ∧
    (∀ K L : sfRationalConstructibleCategory l E X,
      (@pullbackTensorRationalBraiding l _ F _ _ _ X
        (RationalVerdier.units D l hl X)
        ((RationalVerdier.scalar l X E F ι).obj L)
        ((RationalVerdier.scalar l X E F ι).obj K)).hom ≫
      (@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
        (RationalVerdier.units D l hl X)).inv.app (K, L) =
      (@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
        (RationalVerdier.units D l hl X)).inv.app (L, K) ≫
      (RationalVerdier.scalar l X E F ι).map
        ((@pullbackTensorRationalBraiding l _ E _ _ _ X
          (RationalVerdier.units D l hl X) L K).hom)) := by
  sorry

end WeilConjectures
