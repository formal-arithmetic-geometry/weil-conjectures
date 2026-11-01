/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineScalarBaseSmul

/-! # Ordinary sheaf evaluation square

Source: blueprint sk-def-sp-tate-twist-locally-free, Proof (3).
(blueprint: lem-pur-completed-line-sheaf-evaluation-square)
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct MonoidalCategory
universe t u
namespace WeilConjectures
namespace CompletedLineTensor
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedScalarTensorSection
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)
/-- The ordinary sheaf evaluation square before passage to the derived category.
Source: Stacks 03EL, 03EO; blueprint
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/sk-def-sp-tate-twist-locally-free.md,
Proof (3), inverse tensor
evaluation and scalar compatibility
(blueprint: lem-pur-completed-line-sheaf-evaluation-square).
Proof: both sides are morphisms out of the ordinary extension of `(M ⊗ L^m) ⊗ L^{-m}`,
so by the tensor-generator extensionality for `completedScalarTensorSection` it suffices
to compare them on `s ⊗ ((x ⊗ a) ⊗ f)`. The third clause of `IsPairNormalized`, applied at
`-m` and then (under `T_{N,-m}`) at `m`, sends this section to
`((s ⊗ x) ⊗ β_m(1 ⊗ a)) ⊗ β_{-m}(1 ⊗ f)`. The section formula of `evaluation`
(`evaluation_existsUnique`) turns it into `pairing_N(β_m(1 ⊗ a), β_{-m}(1 ⊗ f)) • (s ⊗ x)`.
The pairing clause of `IsPairNormalized` (with `s = t = 1`; for `m < 0` the pairing is the
same Hom evaluation with the factors interchanged; for `m = 0` the first clause at `n = 0`
gives the unit comparison and the pairing is multiplication) identifies the scalar with
`φ(pairing_L(a, f))`. By `completed_scalar_base_smul` this equals
`s ⊗ (pairing_L(a, f) • x)`, which is the image of the generator under the extension of
`evaluation_L`, again by the section formula of `evaluation`. -/
theorem completed_sheaf_evaluation_square (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (M : integralTowerModules l E X) :
    (d.ordinarySheaf (-m)).hom.app ((sheaf l E X L m).obj M) ≫
      (sheaf l F X N (-m)).map ((d.ordinarySheaf m).hom.app M) ≫
      (evaluation l F X N m).hom.app ((completedOrdinaryScalarExtension l E F ι X).obj M) =
    (completedOrdinaryScalarExtension l E F ι X).map
      ((evaluation l E X L m).hom.app M) := by sorry

end CompletedLineTensor
end WeilConjectures
