/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RationalOperationsData
public import Sheaf.Paper.IntegralResidueTor

/-! Bridge theorem for the integral dualizing exceptional value.

Source: prop-coef-integral-dualizing, first proof paragraph.
(blueprint: lem-sf-rational-dualizing-identification-integral-bridge).

The normalized integral exceptional adjunction identifies the exceptional value of the
integral coefficient unit with the coherent integral dualizing object. This is the
integral part of the rational dualizing identification and is strictly simpler than
its localization to the rational category.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalOperations
open ConstructibleExceptionalCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Integral exceptional value of the canonical coefficient unit.
Source: prop-coef-integral-dualizing, proof paragraph 1
(blueprint: lem-sf-rational-dualizing-identification-integral-bridge).
-/
theorem integralDualizing_exceptional_unit_bridge
    (S : structureSystem l X D hl Ω) (F : FieldStage.{u} l)
    (w : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier)
    (U : C l Ω (Spec (.of D.k)) (.integral F))
    (hU : Nonempty ((RingStage.inclusion l Ω (Spec (.of D.k)) (.integral F)).obj U ≅
      integralConstantCoefficientObject l F.carrier (Spec (.of D.k)))) :
    Nonempty ((RingStage.inclusion l Ω X (.integral F)).obj
      ((S.ring.operation (integralDualizingCompactification D X)
        (.integral F)).G.obj U) ≅ w.omega.obj) := by
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    RationalVerdier.units D l hl (Spec (.of D.k))
  sorry

end RationalOperations
end WeilConjectures
