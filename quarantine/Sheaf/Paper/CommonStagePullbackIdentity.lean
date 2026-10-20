/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.RationalCoefficientCategoryComparison
import Sheaf.Paper.CoherentRationalPullbackIdentity

/-! # Identity comparison for common-stage pullback

Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tag 099N.
(blueprint: lem-sf-common-stage-pullback-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients

private theorem transport_heq {C : Type*} [Category C] {A B A' B' : C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  subst A'
  subst B'
  simpa using eq_of_heq h


/-- The recorded common-stage pullback along the identity is naturally the identity.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tag 099N
(blueprint: lem-sf-common-stage-pullback-identity).
Proof: apply coherentRationalPullbackIdentity to the given simultaneous realization
system on the noetherian finite-dimensional scheme X. Copy the chosen common-stage
pullback functor to its prescribed literal object map. At each pair (E,K), apply the
stage inclusion functor to the rational identity isomorphism at E. Every arrow has a
representative at a common finite stage L. The pullback specification conjugates its
rational pullback by the two prescribed scalar comparisons. Rewrite the components
at L and use scalar compatibility to cancel the target comparison. Rational naturality
moves the unit past the representative, and scalar compatibility at the source gives
the desired naturality equation. Compose the resulting natural isomorphism with the
object-copy comparison. The hypotheses are inherited by the finite-type geometric
fibres used in the direct-image module; separatedness and nonemptiness are unnecessary. -/
theorem commonStageDerivedPullback_identity
    (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (S : FdCoefficientComparisonSystem.{u} l Ω)
    (hs : FdComparisonSchemeCoherence l Ω S)
    (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] :
    Nonempty (commonStageDerivedPullback l Ω (𝟙 X) ≅ 𝟭 _) := by
  obtain ⟨e, he⟩ := coherentRationalPullbackIdentity l Ω S hs X
  let F := commonStageDerivedPullback l Ω (𝟙 X)
  have hobj := (commonStageDerivedPullback_existsUnique l Ω (𝟙 X)).exists.choose_spec.1
  let F' := F.copyObj (commonStagePullbackObject l Ω (𝟙 X))
    (fun P ↦ eqToIso (hobj P))
  have hmap (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (L : Index l Ω) (hP : P.stage ≤ L) (hQ : Q.stage ≤ L)
      (a : P.toStage hP ⟶ Q.toStage hQ) :
      F'.map (ofHom P Q L hP hQ a) =
        ofHom (commonStagePullbackObject l Ω (𝟙 X) P)
          (commonStagePullbackObject l Ω (𝟙 X) Q) L hP hQ
          ((commonStagePullbackComparison l Ω (𝟙 X) P L hP).hom ≫
            (rationalDerivedPullback l (Coefficient.{u} l Ω L) (𝟙 X)).map a ≫
            (commonStagePullbackComparison l Ω (𝟙 X) Q L hQ).inv) := by
    exact transport_heq (hobj P) (hobj Q) _ _
      ((commonStageDerivedPullback_existsUnique l Ω (𝟙 X)).exists.choose_spec.2
        P Q L hP hQ a)
  let c : F' ≅ 𝟭 _ := NatIso.ofComponents
    (fun P ↦ (stageSystem l Ω X).ι P.stage |>.mapIso ((e P.stage).app P.obj))
    (by
      intro P Q a
      induction a using StageSystem.PairCategory.hom_induction with
      | h L hP hQ a =>
        rw [hmap P Q L hP hQ a]
        dsimp only [Functor.id_map]
        simp only [Functor.mapIso_hom, Iso.app_hom]
        rw [StageSystem.ι_map_eq hQ, StageSystem.ι_map_eq hP]
        rw [StageSystem.PairCategory.mkHom_comp_mkHom,
          StageSystem.PairCategory.mkHom_comp_mkHom]
        apply congrArg (ofHom (commonStagePullbackObject l Ω (𝟙 X) P) Q L hP hQ)
        have hQ' := he Q L hQ
        have hP' := he P L hP
        rw [Category.assoc, Category.assoc, ← hQ']
        simp only [Iso.inv_hom_id_assoc]
        rw [(e L).hom.naturality, ← Category.assoc]
        exact congrArg (fun b ↦ b ≫ a) hP')
  exact ⟨F.isoCopyObj _ _ ≪≫ c⟩

end WeilConjectures
