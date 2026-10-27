/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.Paper.FiniteConstructibleComplexHeartPresentations
import Sheaf.Paper.FiniteConstructibleComplexHeartCd
import Sheaf.Paper.CondensedSectionsIndVanishing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Torsion-dimension bounds for filtered finite-complex hearts

This is the finite-stage estimate and filtered-colimit assembly on an arbitrary affine.
It does not assert that the weak Serre hull has such presentations.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

set_option synthInstance.maxSize 4096 in
/-- The torsion-dimension estimate extends to every filtered colimit of finite
constructible complex hearts, without a Noetherian hypothesis.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), and the finite-heart coefficient estimate
(blueprint: lem-sfb-torsion-cd-ind-finite-heart).
Proof: apply the finite-heart estimate at the identity pro-etale object. Its pullback
is canonically the identity. Transport along the isomorphism in each finite-heart
presentation, then apply filtered continuity to the diagram of degree-zero modules.
Every source cohomology group is zero, so its colimit is zero. No closure under
kernels or lifting of the diagram's arrows to complexes is used. -/
theorem torsionCd_indFiniteHeart_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsAffine X] (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : indFiniteConstructibleComplexHearts Λ X M)
    (q : ℤ) (hq : (d : ℤ) + 2 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((condensedModuleSections Λ X).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  apply condensedModuleSections_ind_isZero Λ X (finiteConstructibleComplexHearts Λ X)
    q ?_ M hM
  rintro N ⟨K, hK, ⟨e⟩⟩
  let U : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  have : IsAffine U.left := by change IsAffine X; infer_instance
  have hzero := finite_constructible_complex_heart_cohomology_vanishes
    ℓ Λ hΛ X d hcd K hK.1 hK.2 U q hq
  let F := DerivedCategory.singleFunctor _ 0 ⋙
    (condensedModuleSections Λ X).rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ q
  let e' : (CondensedRing.upperStar Λ U.hom).obj (K.homology 0) ≅ N :=
    (CondensedRing.upperStarId Λ X).app (K.homology 0) ≪≫ e.symm
  exact hzero.of_iso (F.mapIso e').symm

end AlgebraicGeometry.ProEtale
