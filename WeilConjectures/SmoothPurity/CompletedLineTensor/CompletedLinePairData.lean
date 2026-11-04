/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLinePowerComparison
public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarOrdinaryCoherence
import WeilConjectures.SixFunctors.Finite.FiniteFreeScalarCochainProperties
import all WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Normalized ordinary comparisons between scalar extension and line tensor

Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).

For a comparison `b` between the scalar extension of a line `L` and a line `N`, there is
a unique `PairData` satisfying `IsPairNormalized`. Its derived comparison satisfies the
counit normalization on every complex, and the comparisons for a three-field tower
are compatible with the ordinary associator.

## Main statements

* `pairData_exists`, `pairData_unique`: existence and uniqueness of normalized data.
* `pairData_ordinary_tower`: compatibility with the ordinary associator.
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

/-- Normalized ordinary comparisons exist; the derived comparison satisfies the counit
normalization on every complex, not only on good ones.
Source: Stacks 03EL, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: take the normalized signed-power comparisons. The binary tensor comparison followed
by the power comparison on the second factor gives the sheaf comparison with the displayed
pure-tensor formula. Finite free extension has invertible universal counits on every
complex, and line tensor is exact, so the composite of the localized termwise comparison
with these invertible maps descends through the localization to the derived category. -/
theorem pairData_exists (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    ∃ d : PairData l E X F ι L N, IsPairNormalized l E X F ι L N b d ∧
      ∀ (m : ℤ) (P : CochainComplex (integralTowerModules l E X) ℤ),
        (completedDerivedScalarExtension l E F ι X).map ((factors l E X L m).hom.app P) ≫
            completedScalarCounit l E F ι X ((complex l E X L m).obj P) ≫
            DerivedCategory.Q.map
              ((comparisonComplex l E X F ι L N m (d.ordinarySheaf m)).hom.app P) =
          (d.ordinary m).hom.app (DerivedCategory.Q.obj P) ≫
            (tensor l F X N m).map (completedScalarCounit l E F ι X P) ≫
            (factors l F X N m).hom.app ((completedOrdinaryScalarComplex l E F ι X).obj P) := by
  sorry

/-- Normalized ordinary comparisons are unique.
Source: Stacks 03EL, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the signed-power comparisons are unique by `line_unique`. The sheaf comparison is
fixed on pure tensors, which generate locally. On good complexes the counit at the source
and the target are invertible, so the derived comparison is fixed on the good
localization, which determines natural transformations. -/
theorem pairData_unique (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    {d d' : PairData l E X F ι L N} (hd : IsPairNormalized l E X F ι L N b d)
    (hd' : IsPairNormalized l E X F ι L N b d') : d = d' := by
  sorry

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)

/-- The ordinary derived line comparisons commute with the ordinary associator.
Source: blueprint Proof (3), final sentence
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: on pure tensors both sheaf paths send t tensor (s tensor (x tensor a)) to
(t j(s) tensor x) tensor b_20(1 tensor a), by `line_tower`. The counit normalizations of
the line comparisons (on every complex) and of the associator transport this termwise
identity to the derived identity on good complexes; localization concludes. -/
theorem pairData_ordinary_tower (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
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
    {d10 : PairData l E X F ι L N} {d21 : PairData l F X G j N P}
    {d20 : PairData l E X G (j.comp ι) L P}
    (h10 : IsPairNormalized l E X F ι L N b10 d10)
    (h21 : IsPairNormalized l F X G j N P b21 d21)
    (h20 : IsPairNormalized l E X G (j.comp ι) L P b20 d20)
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X)) :
    (completedDerivedScalarExtension l F G j X).map ((d10.ordinary m).hom.app K) ≫
      (d21.ordinary m).hom.app ((completedDerivedScalarExtension l E F ι X).obj K) ≫
      (tensor l G X P m).map ((associatorData l E X F ι G j).derived.hom.app K) =
    (associatorData l E X F ι G j).derived.hom.app ((tensor l E X L m).obj K) ≫
      (d20.ordinary m).hom.app K := by
  sorry

end CompletedLineTensor
end WeilConjectures
