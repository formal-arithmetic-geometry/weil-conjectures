/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
import WeilConjectures.SixFunctors.RationalOperations.IntegralDualizingExceptionalUnitBridge
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor

/-! # The rational dualizing object and the structure exceptional adjoint

Source: lem-coef-rational-operations, step 11
(blueprint: lem-sf-rational-dualizing-identification).
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

/-- The dualizing object is the exceptional value of the actual coefficient unit.
Source: lem-coef-rational-operations, DAG proof step 11
(blueprint: lem-sf-rational-dualizing-identification).

Proof: the integral exceptional adjunction at the structure morphism identifies its
value on the completed regular module with the coherent integral dualizing object.
The bridge theorem supplies this integral comparison. Localizing it and applying the
right comparison in the normalized rationalization comparison of `S` gives the
claimed isomorphism; the canonical integral unit localizes definitionally to
`coefficientUnit`.
-/
theorem rationalDualizing_identification
    (S : structureSystem l X D hl Ω) (F : FieldStage.{u} l)
    (w : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier) :
    DualizingIdentification l X D hl Ω S F w := by
  letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
    RationalVerdier.units D l hl (Spec (.of D.k))
  letI : ∀ x : X, Invertible (l : X.residueField x) :=
    RationalVerdier.units D l hl X
  let U : C l Ω (Spec (.of D.k)) (.integral F) :=
    ⟨integralConstantCoefficientObject l F.carrier (Spec (.of D.k)),
      (integral_residue_tor D l hl F.carrier (Spec (.of D.k))).2 ▸
        (integralConstantCoefficient_constructible l F.carrier
          (Spec (.of D.k)) D hl).2.1⟩
  have hU : Nonempty ((RingStage.inclusion l Ω (Spec (.of D.k)) (.integral F)).obj U ≅
      integralConstantCoefficientObject l F.carrier (Spec (.of D.k))) := by
    exact ⟨Iso.refl _⟩
  obtain ⟨e⟩ := integralDualizing_exceptional_unit_bridge D l hl X Ω S F w U hU
  let hEq := (integral_residue_tor D l hl F.carrier X).2
  let Gsf : sfIntegralConstructibleCategory l F.carrier X :=
    ⟨((S.ring.operation (integralDualizingCompactification D X)
        (.integral F)).G.obj U).obj,
      hEq.symm ▸ ((S.ring.operation (integralDualizingCompactification D X)
        (.integral F)).G.obj U).property⟩
  let eCat : Gsf ≅ w.omega :=
    (sfIntegralConstructible l F.carrier X).isoMk e
  let c := integralDualizingCompactification D X
  let b := (S.fields.rationalizationComparison c F).b
  have hu : (rationalization l Ω F (Spec (.of D.k))).obj U =
      coefficientUnit l F.carrier (Spec (.of D.k)) D hl := by
    rfl
  refine ⟨?_
    ⟩
  rw [← hu]
  simpa [DualizingIdentification, coefficientUnit, rationalization, U, Gsf, c, b] using
    ((sfRationalConstructibleLocalization l F.carrier X).mapIso eCat.symm ≪≫
      b.app U)

end WeilConjectures.RationalOperations
