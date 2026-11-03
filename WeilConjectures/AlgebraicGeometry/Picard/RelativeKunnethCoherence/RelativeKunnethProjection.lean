/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeKunnethStatement
public import WeilConjectures.AlgebraicGeometry.Picard.RelativeKunnethCoherence.RelativeKunnethCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
import WeilConjectures.AlgebraicGeometry.RelativeKunnethInverseWord
import WeilConjectures.AlgebraicGeometry.RelativeKunnethIdentityComparisons
import WeilConjectures.AlgebraicGeometry.SfIdentityProjectionNormalization

/-! # One compatibility of the relative product -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.RelativeKunnethCoherence

/-- Projection normalization of the identity-factor relative product.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, clause (iv)
(blueprint: lem-sf-relative-kunneth-projection).

Proof: expand the inverse relative product with
relativeKunnethIsoOfIsPullback_inverse_word in the square (1_X,f,f,1_B). The right
composition unit identifies its last factor with the compact-support identity comparison.
The identity-square base-change equation identifies its exchange with the pullback identity
comparisons on X and B. The identity projection normalization removes the projection for
1_B. Naturality of the tensor symmetry and of PF_f moves these identity comparisons
through the word. The two signed symmetries then cancel, leaving PF_f, preceded by the
compact-support identity comparison on the second tensor factor and followed by Rf_! of
the inverse pullback identity on the first factor. The identity comparison constructed from
the identity compactification agrees with rightDerivedLowerShriekIdIso: transport the
proper forget-supports comparison through exact derivation and use the identity counit.
These substitutions give exactly the displayed tensorIso maps, in their stated order.
-/
theorem relativeKunneth_projection
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k]
    [HasTateTwist Λ] [HasInvertibleExponent Λ (Spec (.of k))]
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    [HasCompactification aB] :
    (∀ {X : Scheme.{u}} (f : X ⟶ B)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [HasCompactification f] [HasCompactification (f ≫ aB)]
      (_Sf : SixFunctorDatum Λ k f aB)
      (K : DerivedCategoryModule Λ X) (L : DerivedCategoryModule Λ B)
      (_hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
      (_hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) B L),
      (relativeKunnethIsoOfIsPullback Λ (IsPullback.id_horiz f) f (by simp) K L).inv =
        (tensorIso (Iso.refl ((R(f)_![ModuleCat.{u + 1} Λ]).obj K))
          ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) B).app L)).hom ≫
        ((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app L ≫
        (R(f)_![ModuleCat.{u + 1} Λ]).map
          (tensorIso ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).app K).symm
            (Iso.refl _)).hom) := by sorry

end WeilConjectures.RelativeKunnethCoherence
