/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData
import Sheaf.AlgebraicGeometry.AffineRawEvaluationTypedPullback
import Sheaf.AlgebraicGeometry.AffineComparisonPullback

/-! # Restriction of the normalized coherent raw comparison

Source: Stacks Project, Tags 03Q8, 03FD and 03P2.
-/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] RingedSpace.moduleCohomology
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived
  CategoryTheory.derivedExtEvaluation coherentEtaleRestrictionIso
  CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.comp
  CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Functor.rightDerived CategoryTheory.Functor.rightDerivedFunctor
  Etale.cohomologyMap CategoryTheory.Sheaf.H.map
  CategoryTheory.Adjunction.homEquiv
  coherentEtaleMap qcoherentPullbackSection
  moduleCohomologyFMap IsNormalizedCoherentEtaleComparison
  tensorPullback tensorPullbackObj tensorSectionsComp tensorSectionsUnit
  etaleTensorSectionsRestriction affineRealizationRestriction affineRealizationComparison
  affineRealizationAffineComparison affineRealizationRawEvaluation affineRealizationRawEquiv
  Etale.rawRestrictedCohomologyComparison
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

/-- Raw evaluation followed by normalized coherent comparison commutes with
restriction between affine etale objects.
Source: Stacks Project, Tags 03Q8, 03FD and 03P2.
(blueprint: lem-weil-pbc-affine-cohomology-raw-restriction).

Proof: The raw-restricted class normalization identifies the restriction of a
raw class with cohomological pullback along the induced map of fibre products,
followed by inverse-image composition on coefficients. Evaluation at the integer
generator identifies this derived-sections pullback with the Ext presentation of
cohomological pullback: both evaluate the pulled-back cocycle at the restricted
generator. The etale restriction coefficient isomorphism then changes the
coefficient to the tensor pullback of G. Its defining formula on tensor sections
identifies the resulting coefficient map with tensor-pullback composition.
Apply the normalized comparison pullback square to that map and the canonical
normalized comparisons on both fibre products. Their hypotheses hold because
the base objects are affine and f is quasi-compact and separated. The structural
section formula identifies its adjunct with precisely the coefficient map above.
The resulting ordinary cohomology map is affineRealizationRestriction. This
argument also includes empty objects, zero coefficients and q=0. -/
theorem affineRealizationRawComparison_natural {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left]
    (h : V' ⟶ V)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op V)) :
    affineRealizationAffineComparison f G q V'
        (affineRealizationRawEvaluation f G q V'
          ((Etale.abelianHigherDirectImageRawPresheaf f q
            (liftedCoherentEtaleSheaf G)).map h.op z)) =
      affineRealizationRestriction f G q h
        (affineRealizationAffineComparison f G q V
          (affineRealizationRawEvaluation f G q V z)) := by
  obtain ⟨θ, hθ, hsquare⟩ := affineRealizationComparison_pullback f G q V V' h
  exact (congrArg (affineRealizationAffineComparison f G q V')
    (affineRealizationRawEvaluation_typed_pullback f G V V' h θ hθ q z)).trans
    (hsquare (affineRealizationRawEvaluation f G q V z))

/-- Bundled naturality of the same fixed raw-coherent comparison.
Source: Stacks Project, Tags 03Q8, 03FD and 03P2
(blueprint: lem-weil-pbc-affine-cohomology-raw-restriction).
Proof: substitute the evaluation formula on both sides of the raw restriction square. -/
theorem affineRealizationRawCoherentEquiv_natural {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left]
    (h : V' ⟶ V) (z : affineRealizationRawGroup f G q V) :
    affineRealizationRawCoherentEquiv f G q V'
        (affineRealizationRawRestriction f G q h z) =
      affineRealizationRestriction f G q h (affineRealizationRawCoherentEquiv f G q V z) := by
  exact (affineRealizationRawCoherentEquiv_apply f G q V' _).trans
    ((affineRealizationRawComparison_natural f G q V V' h z).trans
      (congrArg (affineRealizationRestriction f G q h)
        (affineRealizationRawCoherentEquiv_apply f G q V z).symm))

end
end AlgebraicGeometry.Scheme.Modules
