/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.Paper.IntegralTwistBaseChangeDefinitions
public import Sheaf.Paper.CoefficientTwistsDetailed
public import Sheaf.Paper.PurIntegralTwistLineInverseImage
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.IntegralTwistSchemeCompatibility

/-! # Completed integral twist base change

Source: main-20261015 blueprint, sec-six-functors-basics/sk-prop-sf-existence,
`prop-weil-twist-preserves.proof.md`, first and final sentences
(blueprint: lem-weil-integral-twist-base-change).

The line, coefficient inclusion and scalar-extension isomorphism are the published
constructions of `def-coefficient-twists-detailed`. Scheme naturality is expressed
on their underlying semilinear maps, using the actual inverse-image adjunction.
The helper predicates specify the pullback identifications by roots, powers and evaluation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Canonical scalar base change of all signed integral Tate lines, with evaluation,
tensor-power, tower and scheme compatibility.
Source: first and final sentences of `prop-weil-twist-preserves.proof.md`
(blueprint: lem-weil-integral-twist-base-change).

Proof:
1. The normalization clause is the existence half of the uniqueness theorem
   `twistScalarMaps_existsUnique`, of which `twistScalarMaps` is the chosen witness.
2. The pure-tensor formula of the scalar-extension isomorphism is likewise the
   existence half of `twistLineScalarIso_existsUnique`, in every degree m.
3. Tower compatibility of the semilinear maps is `twistScalarMaps_composition`.
4. Scheme naturality (the coefficient, root and signed inverse-image comparisons,
   their normalizations and the scalar squares in every degree) is the geometric
   lemma `integral_twist_base_change_scheme`
   (blueprint: lem-weil-integral-twist-scheme-compatibility).
-/
theorem integral_twist_base_change
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)] :
    IsCanonicalTwistScalarMaps l E S F ι (twistScalarMaps l E S F ι) ∧
    (∀ (m : ℤ) (U : S.ProEtᵒᵖ)
        (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U)
        (x : (integralTwistLine l E S m).val.obj U),
      (twistLineScalarIso l E S F ι m).hom.val.app U
          (integralOrdinaryTensorSection l E F ι S _ U b x) =
        b • (@id ((integralTwistLine l F S m).val.obj U)
          ((twistScalarMaps l E S F ι m).val.app U x))) ∧
    (∀ (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
        (κ : F →ₐ[Padic l] G) (m : ℤ) (U : S.ProEtᵒᵖ)
        (x : (integralTwistLine l E S m).val.obj U),
      (twistScalarMaps l E S G (κ.comp ι) m).val.app U x =
        (twistScalarMaps l F S G κ m).val.app U
          ((twistScalarMaps l E S F ι m).val.app U x)) ∧
    ∀ (X : Scheme.{u}) (h : X ⟶ S)
        [∀ x : X, Invertible (l : X.residueField x)],
      ∃ (αE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
          (completedIntegralCommRingSheafUnrestricted l E S) ⟶
            completedIntegralCommRingSheafUnrestricted l E X)
        (αF : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
          (completedIntegralCommRingSheafUnrestricted l F S) ⟶
            completedIntegralCommRingSheafUnrestricted l F X)
        (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
          (purTwistZlOne S l) ⟶ purTwistZlOne X l)
        (ρE : ∀ m : ℤ, (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
          (integralTwistUnderlying l E S m) ≅ integralTwistUnderlying l E X m)
        (ρF : ∀ m : ℤ, (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
          (integralTwistUnderlying l F S m) ≅ integralTwistUnderlying l F X m),
        (IsIso αE ∧ IsPurIntegralCoefficientComparison h l E αE) ∧
        (IsIso αF ∧ IsPurIntegralCoefficientComparison h l F αF) ∧
        (IsIso τ ∧ IsPurRootLimitComparison h l τ) ∧
        IsIntegralTwistInverseComparison l E h αE τ ρE ∧
        IsIntegralTwistInverseComparison l F h αF τ ρF ∧
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
            (integralCompletedScalarMap l E F ι S) ≫ αF =
          αE ≫ integralCompletedScalarMap l E F ι X ∧
        ∀ m : ℤ,
          (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
              (integralTwistScalarUnderlying l E S F ι m) ≫ (ρF m).hom =
            (ρE m).hom ≫ integralTwistScalarUnderlying l E X F ι m := by
  refine ⟨(twistScalarMaps_existsUnique l E S F ι).exists.choose_spec, ?_, ?_, ?_⟩
  · intro m
    exact (twistLineScalarIso_existsUnique l E S F ι m).exists.choose_spec
  · intro G _ _ _ κ m U x
    exact twistScalarMaps_composition l E S F ι G κ m U x
  · exact integral_twist_base_change_scheme l E F ι S

end WeilConjectures
