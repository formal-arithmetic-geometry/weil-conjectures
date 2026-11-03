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
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
import WeilConjectures.SmoothPurity.CompletedScalarAssociator.PrescribedScalarAssociator
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare

/-! Main simultaneous normalization theorem.
- (blueprint: lem-sp-proetale-pullback-scalar-tower-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Simultaneous normalization of the prescribed pullback and scalar associators,
with their scalar-tower identity, naturally for every unbounded derived object.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-direct-image.proof.md, Step 4 and the Step 1 counit transpose
(blueprint: lem-sp-proetale-pullback-scalar-tower-normalization).

Proof:
1. Choose compatible flat-term K-flat representatives. Apply
   lem-sfb-successive-derived-quotient-normalization to the associator prescribed
   by det-sp-scalar-extension-functor. The successive scalar normalization gives
   (x tensor s) tensor t mapping to x tensor psi(s)t and
   the inverse inserting 1. The prescribed pullback comparison is the balanced
   map q-inverse(x tensor s) mapping to q-inverse(x) tensor c_B(q-inverse(s)).
   Functoriality of the constant-section maps gives both coefficient squares.
2. On q-inverse((x tensor s) tensor t), both routes in the stated identity give
   q-inverse(x) tensor c_C(q-inverse(psi(s)t)). Balancing, multiplicativity and
   the coefficient squares identify these expressions in every degree.
3. Restrictions, sheafification and the signed total differentials preserve the
   formulas. Use the balanced map of def-sp-reduction-direct-image-comparison.
   The universal scalar counits and exact pullback localization factors
   identify these maps with the specified derived maps. Resolving every object
   and using naturality proves independence and uniqueness for all compatible
   representatives. It also descends the equality to every unbounded K. No
   flatness of the coefficient maps or direct-image projection is used.
-/
theorem proEtalePullbackScalarTowerNormalization
    (ℓ : ℕ) [Fact ℓ.Prime]
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (_hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (_hC : ∃ n : ℕ, (ℓ : C) ^ n = 0)
    (φ : A →+* B) (ψ : B →+* C) {Z Y : Scheme.{u}} (q : Z ⟶ Y) :
    ((proEtaleConstantRingComparison q A).hom ≫ proEtaleConstantRingMap (T := Z) φ =
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
        (proEtaleConstantRingMap (T := Y) φ) ≫ (proEtaleConstantRingComparison q B).hom) ∧
    ((proEtaleConstantRingComparison q B).hom ≫ proEtaleConstantRingMap (T := Z) ψ =
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
        (proEtaleConstantRingMap (T := Y) ψ) ≫ (proEtaleConstantRingComparison q C).hom) ∧
    PrescribedScalarTowerNormalization φ ψ Y ∧
    PrescribedScalarTowerNormalization φ ψ Z ∧
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
  have hφ := coeffSquare φ q
  have hψ := coeffSquare ψ q
  have hY := scalarTowerNormalization_package φ ψ Y
  have hZ := scalarTowerNormalization_package φ ψ Z
  have hp := pullbackNormalization_package ℓ _hA _hB _hC φ ψ q
  exact ⟨hφ, hψ, hY, hZ, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

end AlgebraicGeometry.ProEtale
