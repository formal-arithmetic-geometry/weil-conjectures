/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- Pullback normalization for the three coefficient maps and their scalar cocycle.
Source: Stacks 03EL, 06YY, 07A4.

Proof: define the ordinary balanced comparison on pure sections using inverse image
and the constant-ring comparison. The coefficient comparison squares make this map
linear and identify both orders of successive scalar extension on pure tensors.
Sheafification and termwise extension preserve the equality of chain maps. Resolve
every unbounded object by flat-term K-flat complexes and descend along localization;
the scalar counits and exact pullback factors identify the descended maps with the
prescribed comparisons. Their universal properties give uniqueness and the cocycle.
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization-pullback-package). -/
theorem pullbackNormalization_package
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (_hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (_hC : ∃ n : ℕ, (ℓ : C) ^ n = 0)
    (φ : A →+* B) (ψ : B →+* C) {Z Y : Scheme.{u}} (q : Z ⟶ Y) :
    PrescribedPullbackScalarNormalization φ q ∧
      PrescribedPullbackScalarNormalization ψ q ∧
      PrescribedPullbackScalarNormalization (ψ.comp φ) q ∧
      ∀ K : proEtaleDerivedCategory Y A,
        (proEtaleConstantRingDerivedPullback C q).map
            ((scalarExtensionFunctor_composition φ ψ Y).hom.app K) ≫
          (directImageScalarPullbackIso (ψ.comp φ) q).hom.app K =
        (directImageScalarPullbackIso ψ q).hom.app ((scalarExtensionFunctor φ Y).obj K) ≫
          (scalarExtensionFunctor ψ Z).map ((directImageScalarPullbackIso φ q).hom.app K) ≫
          (scalarExtensionFunctor_composition φ ψ Z).hom.app
            ((proEtaleConstantRingDerivedPullback A q).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale
