/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentHigherImageClasses
import Sheaf.AlgebraicGeometry.SheafHDerivedNaturality

/-! # Local scalars and restriction before higher-image sheafification

Source: Stacks Project, Tags 03Q8 and 03DR.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
attribute [local irreducible] affineRealizationRawEquiv coherentEtaleMap
  tensorPullback tensorPullbackObj coherentEtaleRestrictionIso
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived CategoryTheory.derivedExtEvaluation
  Etale.rawRestrictedCohomologyComparison
  Etale.rawAffineComplexPullback
  Etale.upperStarComp
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance

private theorem evaluation_coefficient_iso {Y : Scheme.{u}}
    {F F' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (K : F ≅ F') (q : ℕ)
    (x : (Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F))) :
    Etale.sheafHToDerived F' q
        (Sheaf.H.map K.hom q ((Etale.sheafHDerivedEquiv F q).symm x)) =
      (Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map K.hom)) x := by
  have he : Etale.sheafHToDerived F q ((Etale.sheafHDerivedEquiv F q).symm x) = x := by
    unfold Etale.sheafHDerivedEquiv
    exact (Equiv.ofBijective _ (Etale.sheafHToDerived_bijective F q)).apply_symm_apply x
  exact (Etale.sheafHToDerived_map K.hom q _).trans (congrArg
    ((Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).map
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map K.hom))) he)

private theorem evaluation_full_iso {Y : Scheme.{u}}
    {F F' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (K : F ≅ F') (q : ℕ) {A : AddCommGrpCat.{u + 1}}
    (c : A ≅ (Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F))) (z : A) :
    Etale.sheafHToDerived F' q
      ((c.addCommGroupIsoToAddEquiv.trans
        ((Etale.sheafHDerivedEquiv F q).symm.trans
          (((Sheaf.functorH _ q).mapIso K).addCommGroupIsoToAddEquiv))) z) =
      (Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map K.hom))
          (c.hom z) := by
  dsimp only [AddEquiv.trans_apply]
  exact evaluation_coefficient_iso K q _

/-- The fixed raw evaluation has its displayed coefficient-transport formula.
Source: Stacks Project, Etale Cohomology Tags 03Q8, 03FD and 01FT.
(blueprint: lem-weil-pbc-coherent-raw-evaluation-formula).
Proof: expand affineRealizationRawEquiv into rawRestrictedCohomologyComparison,
the inverse of sheafHDerivedEquiv, and cohomology of coherentEtaleRestrictionIso.
Apply sheafHToDerived_map to the last coefficient morphism. The forward map of
sheafHDerivedEquiv is sheafHToDerived by its construction from Equiv.ofBijective;
hence it cancels its inverse. The remaining composite is precisely the right hand
side. This assertion concerns the evaluation equivalence alone and has no chart
restriction or scalar. In degree zero the same inverse cancellation applies,
and the empty chart and zero coefficient cases require no nonzero generator. -/
theorem raw_evaluation_formula_aux {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) (V : S.Etale)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op V)) :
    Etale.sheafHToDerived
        (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q
        (affineRealizationRawEquiv f G q V z) =
      (Etale.cohomology AddCommGrpCat.{u + 1} (Limits.pullback V.hom f) (q : ℤ)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
          (coherentEtaleRestrictionIso (pullback.snd V.hom f) G).hom))
            (Etale.rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) V z) := by
  have : IsIso (Etale.rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) V) :=
    Etale.isIso_rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) V
  unfold affineRealizationRawEquiv
  exact evaluation_full_iso (coherentEtaleRestrictionIso (pullback.snd V.hom f) G) q
    (asIso (Etale.rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) V)) z

end AlgebraicGeometry.Scheme.Modules
