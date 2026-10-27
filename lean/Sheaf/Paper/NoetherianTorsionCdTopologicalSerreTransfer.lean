/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.FiniteConstructibleComplexHeartCd
import Sheaf.Paper.FiniteComplexHeartFilteredApproximation
import Sheaf.Paper.CondensedSectionsIndVanishing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# The valid Noetherian torsion-dimension transfer

The Noetherian hypothesis is required by the current finite-heart approximation
lemma. This specialization does not replace the unrestricted affine assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option synthInstance.maxSize 4096 in
/-- The Noetherian specialization of the affine weak-Serre heart vanishing assertion.
Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph;
the repaired Noetherian finite-heart approximation argument
(blueprint: lem-sfb-noetherian-torsion-cd-topological-serre-transfer).
Proof: the finite-complex heart theorem gives the local bound d+2. The Noetherian
approximation theorem makes its filtered-colimit class a replete weak Serre class
closed under the ambient coproducts. Minimality places M in this class. Apply the
filtered-colimit vanishing lemma, using the identity pro-etale test for each finite
heart. The identity inverse-image isomorphism removes the pullback in this test.
-/
theorem torsionCd_topological_serreHeart_cohomology_vanishes_of_locallyNoetherian
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
    (X : Scheme.{u}) [IsAffine X] [IsLocallyNoetherian X] (d : ℕ)
    (hcd : ∀ (V : Scheme.{u}) (v : V ⟶ X) [IsAffine V] [Etale v],
      V.HasTorsionEtaleCohomologicalDimensionLE d)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ X) M)
    (q : ℤ) (hq : (d : ℤ) + 2 < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((condensedModuleSections Λ X).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have hfinite (K) (hK : IsFiniteConstantConstructibleComplex Λ X K)
      (U : X.ProEt) [IsAffine U.left] (r : ℤ) (hr : ((d + 2 : ℕ) : ℤ) < r) :=
    finite_constructible_complex_heart_cohomology_vanishes ℓ Λ hΛ X d hcd
      K hK.1 hK.2 U r (by simpa using hr)
  obtain ⟨_, hgen, hker, hcoker, hext, hsum⟩ :=
    finite_complex_heart_filtered_approximation ℓ Λ hΛ X (d + 2) hfinite
  have : (indFiniteConstructibleComplexHearts Λ X).IsClosedUnderIsomorphisms := by
    unfold indFiniteConstructibleComplexHearts
    infer_instance
  have hind : indFiniteConstructibleComplexHearts Λ X M :=
    hM _ hgen inferInstance hker hcoker hext hsum
  apply condensedModuleSections_ind_isZero Λ X (finiteConstructibleComplexHearts Λ X)
    q ?_ M hind
  rintro N ⟨K, hK, ⟨e⟩⟩
  let U : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  have : IsAffine U.left := by change IsAffine X; infer_instance
  have hzero := hfinite K hK U q (by simpa using hq)
  let F := DerivedCategory.singleFunctor _ 0 ⋙
    (condensedModuleSections Λ X).rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ q
  let e' : (CondensedRing.upperStar Λ U.hom).obj (K.homology 0) ≅ N :=
    (CondensedRing.upperStarId Λ X).app (K.homology 0) ≪≫ e.symm
  exact hzero.of_iso (F.mapIso e').symm

end AlgebraicGeometry.ProEtale
