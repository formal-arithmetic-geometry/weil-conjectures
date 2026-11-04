/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import all WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Scalar extension of signed powers of a coefficient line

Source: Stacks 03EK, 03EO, 0GMX; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).

A comparison `b` between the scalar extension of a line `L` and a line `N` induces
comparisons of all signed powers: positive powers by the binary tensor comparison and
`b`, negative powers by duality. They are uniquely fixed by the positive formula and the
pairing formula, and they are compatible with a tower of three coefficient fields.

## Main definitions and statements

* `IsLineNormalized`: the positive-power formula and the pairing formula.
* `line_exists`, `line_unique`: normalized signed-power comparisons exist and are unique.
* `line_tower`: the comparisons for a three-field tower compose.
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

/-- Comparisons of all signed powers after scalar extension.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
abbrev LineFamily (L : integralTowerModules l E X) (N : integralTowerModules l F X) :=
  ∀ m : ℤ, SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m

/-- The positive-power formula and the pairing formula of `IsPairNormalized`.
Source: Stacks 03EL, 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def IsLineNormalized (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (B : LineFamily l E X F ι L N) : Prop :=
  (∀ n : ℕ,
    (B (Int.ofNat n)).hom = ((binary l E X F ι).power L n).hom ≫
      SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingSheafUnrestricted l F X) b.hom n) ∧
  (∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (f : (power l E X L (-Int.ofNat (n + 1))).val.obj U)
      (x : (power l E X L (Int.ofNat (n + 1))).val.obj U),
    pairing l F X N (Int.ofNat (n + 1)) U
      ((B (Int.ofNat (n + 1))).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) _ U t x))
      ((B (-Int.ofNat (n + 1))).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) _ U s f)) =
      s * t * (completedCoefficientMap l E F ι X).hom.app U
        (pairing l E X L (Int.ofNat (n + 1)) U x f))

/-- Normalized signed-power comparisons exist.
Source: Stacks 03EK, 0GMX; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: positive powers are the binary tensor comparison followed by the tensor power of
`b`. For a negative power, compose the dual scalar comparison, which is invertible on
lines, with precomposition by the inverse positive comparison. Evaluation cancels this
inverse and gives the pairing formula. -/
theorem line_exists (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    ∃ B : LineFamily l E X F ι L N, IsLineNormalized l E X F ι L N b B := by
  sorry

/-- Normalized signed-power comparisons are unique.
Source: Stacks 03EK, 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: positive powers are given by a formula. A negative comparison is determined by its
pairing with the positive comparison: sections of the scalar extension are locally sums
of pure tensors, the positive comparison is invertible, and a section of the dual sheaf is
determined by its values on all restrictions. -/
theorem line_unique (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    {B B' : LineFamily l E X F ι L N} (hB : IsLineNormalized l E X F ι L N b B)
    (hB' : IsLineNormalized l E X F ι L N b B') : B = B' := by
  sorry

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)

/-- Normalized signed-power comparisons are compatible with a three-field tower.
Source: Stacks 03EK, 03EO; blueprint Proof (3), final sentence
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: for positive powers induct on the exponent, using the tower hypothesis on `b` and
the recursive binary formula. For negative powers both sides have the same pairing with
the positive comparisons, by the positive case, so they agree by uniqueness. -/
theorem line_tower (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (P : integralTowerModules l G X) [P.IsFiniteLocallyFreeOfRank 1]
    (b10 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (b21 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l F G j X) N ≅ P)
    (b20 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E G (j.comp ι) X) L ≅ P)
    (hb : ∀ (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : L.val.obj U),
      b21.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l F G j X) N U t
          (b10.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
            max u (t + 1)} (completedCoefficientMap l E F ι X) L U s x))) =
        b20.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l E G (j.comp ι) X) L U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x))
    {B10 : LineFamily l E X F ι L N} {B21 : LineFamily l F X G j N P}
    {B20 : LineFamily l E X G (j.comp ι) L P}
    (h10 : IsLineNormalized l E X F ι L N b10 B10)
    (h21 : IsLineNormalized l F X G j N P b21 B21)
    (h20 : IsLineNormalized l E X G (j.comp ι) L P b20 B20)
    (m : ℤ) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
    (a : (power l E X L m).val.obj U) :
    (B21 m).hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
        max u (t + 1)} (completedCoefficientMap l F G j X) (power l F X N m) U t
        ((B10 m).hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t,
          max u (t + 1), max u (t + 1)} (completedCoefficientMap l E F ι X)
          (power l E X L m) U s a))) =
      (B20 m).hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
        max u (t + 1)} (completedCoefficientMap l E G (j.comp ι) X) (power l E X L m) U
        (t * (completedCoefficientMap l F G j X).hom.app U s) a) := by
  sorry

end CompletedLineTensor
end WeilConjectures
