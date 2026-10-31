/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfLocalizationData

import WeilConjectures.AlgebraicGeometry.ExceptionalCommonStageDescent
import WeilConjectures.AlgebraicGeometry.SfLocalizationFiniteCoherence
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # SfCommonStageLocalizationConstruction

Source: current blueprint, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md.
(blueprint: lem-sf-common-stage-localization-construction). -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open ExceptionalCommonStage
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

private theorem localizationPullbackEquality
    {l : ℕ} [Fact l.Prime] {Ω : Type v} [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] {V W : Scheme.{u}} (f : V ⟶ W)
    [∀ x : V, Invertible (l : V.residueField x)]
    [∀ y : W, Invertible (l : W.residueField y)]
    (F : (stageSystem l Ω W).Morphism (stageSystem l Ω V))
    (hΦ : ∀ E, F.Φ E = rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
    (hβ : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω W E),
      HEq ((F.β h).app K) (commonStagePullbackComparison l Ω f ⟨E, K⟩ L h)) :
    F.functor = commonStageDerivedPullback l Ω f := by
  apply (commonStageDerivedPullback_existsUnique l Ω f).unique (y₁ := F.functor)
  · rcases F with ⟨Φ, β, coh⟩
    have hΦ' : Φ = fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f :=
      funext hΦ
    subst Φ
    constructor
    · intro P
      rfl
    · intro P Q L hP hQ a
      apply heq_of_eq
      change StageSystem.PairCategory.mkHom
        (X := commonStagePullbackObject l Ω f P)
        (Y := commonStagePullbackObject l Ω f Q) L hP hQ
        ((β hP).hom.app P.obj ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map a ≫
          (β hQ).inv.app Q.obj) = _
      have hp := congrArg Iso.hom (eq_of_heq (hβ P.stage L hP P.obj))
      have hq := congrArg Iso.inv (eq_of_heq (hβ Q.stage L hQ Q.obj))
      dsimp only [Iso.app_hom, Iso.app_inv] at hp hq
      rw [hp, hq]
  · exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec

private def supportedOfDescent
    {l : ℕ} [Fact l.Prime] {Ω : Type v} [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] {X Z U : Scheme.{u}}
    (D : FiniteData l Ω X Z U) (hD : Hypotheses D)
    (F : FiniteConclusion D) (R : Descent D F) :
    SfSupportedLocalization (𝟭 (Pair l Ω X)) (𝟭 (Pair l Ω Z)) (𝟭 (Pair l Ω U)) := by
  have hclosedApp : ∀ P, IsIso (R.closedAdj.counit.app P) := by
    rintro ⟨E, P⟩
    have := hD.closedCounit E
    rw [eq_of_heq (R.closedCounit E P)]
    infer_instance
  letI := hclosedApp
  haveI : IsIso R.closedAdj.counit := NatIso.isIso_of_isIso_app _
  let ff := R.closedAdj.fullyFaithfulROfIsIsoCounit
  letI := ff.full
  letI := ff.faithful
  refine {
    iPull := D.closedPull.functor
    jPull := D.openPull.functor
    iPush := D.closedPush.functor
    jPush := D.openPush.functor
    exceptional := (exceptionalSystem D F).functor
    closedAdjunction := R.closedAdj
    openAdjunction := R.openAdj
    exceptionalAdjunction := R.exceptionalAdj
    boundary := R.boundary
    distinguished := R.distinguished
    unique_boundary := ?_
    orthogonal := fun K m ↦ R.orthogonal _ _ m
    exceptional_open_zero := ?_
    exceptional_unit := fun Q ↦ inferInstance }
  · intro K δ hδ
    exact (triangle_morphism_extension _ _ (R.distinguished K)
      (R.distinguished K) (𝟙 K)).2.2 (R.orthogonal _ _ 1) δ hδ
  · intro G
    let H := (exceptionalSystem D F).functor.obj (D.openPush.functor.obj G)
    have hz : Subsingleton (D.closedPush.functor.obj H ⟶ D.openPush.functor.obj G) := by
      let e := (shiftFunctorZero (Pair l Ω X) ℤ).app (D.closedPush.functor.obj H)
      let := R.orthogonal H G 0
      exact (Iso.homCongr e (Iso.refl _)).symm.injective.subsingleton
    let := hz
    have hh : Subsingleton (H ⟶ H) := (R.exceptionalAdj.homEquiv H
      (D.openPush.functor.obj G)).symm.injective.subsingleton
    exact (IsZero.iff_id_eq_zero H).2 (hh.elim _ _)

private theorem stageComparisonOfDescent
    {l : ℕ} [Fact l.Prime] {Ω : Type v} [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] {X Z U : Scheme.{u}}
    (D : FiniteData l Ω X Z U) (hD : Hypotheses D)
    (F : FiniteConclusion D) (R : Descent D F) (E : Index l Ω)
    (S : SfSupportedLocalization (𝟭 (Stage l Ω X E))
      (𝟭 (Stage l Ω Z E)) (𝟭 (Stage l Ω U E)))
    (hc : D.closedPull.Φ E = S.iPull) (ho : D.openPull.Φ E = S.jPull)
    (hi : D.closedPush.Φ E = S.iPush) (hj : D.openPush.Φ E = S.jPush)
    (he : D.exceptional E = S.exceptional)
    (hca : HEq (D.closedAdj E) S.closedAdjunction)
    (hoa : HEq (D.openAdj E) S.openAdjunction)
    (hea : HEq (D.exceptionalAdj E) S.exceptionalAdjunction) :
    Nonempty (SfLocalizationStageComparison S (supportedOfDescent D hD F R)
      (inclusion (Y := X) E) (inclusion (Y := Z) E) (inclusion (Y := U) E)) := by
  rcases S with ⟨ip, jp, ips, jps, ex, ca, oa, ea, bd, hd, hu, hz, hez, heu⟩
  dsimp only at hc ho hi hj he hca hoa hea
  subst ip
  subst jp
  subst ips
  subst jps
  subst ex
  have hca' := eq_of_heq hca
  have hoa' := eq_of_heq hoa
  have hea' := eq_of_heq hea
  subst ca
  subst oa
  subst ea
  refine ⟨{
    closed_push := D.closedPush.ιCompFunctorIso E
    open_push := D.openPush.ιCompFunctorIso E
    exceptional := (exceptionalSystem D F).ιCompFunctorIso E
    open_pull := D.openPull.ιCompFunctorIso E
    counit := ?_
    open_unit := ?_
    unit := ?_ }⟩
  · intro K
    change D.closedPush.functor.map (𝟙 _) ≫ 𝟙 _ ≫
      (inclusion E).map ((D.exceptionalAdj E).counit.app K) =
        R.exceptionalAdj.counit.app ((inclusion E).obj K)
    rw [D.closedPush.functor.map_id, Category.id_comp, Category.id_comp]
    exact (eq_of_heq (R.exceptionalCounit E K)).symm
  · intro K
    change R.openAdj.unit.app ((inclusion E).obj K) ≫
      D.openPush.functor.map (𝟙 _) ≫ 𝟙 _ =
        (inclusion E).map ((D.openAdj E).unit.app K)
    rw [D.openPush.functor.map_id, Category.comp_id]
    erw [Category.comp_id]
    exact eq_of_heq (R.openUnit E K)
  · intro K
    change R.exceptionalAdj.unit.app ((inclusion E).obj K) ≫
      (exceptionalSystem D F).functor.map (𝟙 _) ≫ 𝟙 _ =
        (inclusion E).map ((D.exceptionalAdj E).unit.app K)
    rw [(exceptionalSystem D F).functor.map_id, Category.comp_id]
    erw [Category.comp_id]
    exact eq_of_heq (R.exceptionalUnit E K)

/-- Descend a family of rational supported localizations to algebraically closed
coefficients. Source: supported localization proof, (2) and (3), algebraically closed
coefficient passage (blueprint: lem-sf-common-stage-localization-construction).

Proof: choose each rational record from the given family; all its pullbacks are
already equal to the specified geometric pullbacks. The canonical scalar-extension
comparisons identify closed and open direct images. Their mates identify the
exceptional right adjoints, with equality fixed by preservation of the exceptional
counit. Uniqueness of supported triangles makes these comparisons compatible with
identity inclusions, successive inclusions and shifts. Consequently the five
functors form the finite data and satisfy the normalized hypotheses of
exceptionalCommonStageDescent. Apply that theorem with the canonical geometric
pullback comparisons. Its descended functors, adjunctions and natural boundary
form the supported record. Its pullback identifications give closed_pull and
open_pull; its inclusion comparisons give the three counit and unit equations of
SfLocalizationStageComparison for every finite field. The exact common-stage Hom
colimits preserve closed-to-open orthogonality, hence boundary uniqueness,
exceptional-open vanishing and the invertibility of the exceptional unit.
-/
theorem sfCommonStageLocalizationConstruction
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : k))
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X : Scheme.{u}) (t : X ⟶ Spec (.of k))
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    {Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (stages : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      Nonempty (SfRationalLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) k hl t i j)) :
    Nonempty (SfAlgebraicallyClosedLocalization l Ω k hl t i j) := by
  classical
  let S := fun E ↦ (stages E).some
  obtain ⟨D, hD, hgeom, hS⟩ :=
    sfSupportedLocalization_finite_coherence k l hl Ω X t i j hij S
  obtain ⟨F, R, _⟩ := exceptionalCommonStageDescent k hl t i j hij D hD hgeom
  let A := supportedOfDescent D hD F R
  let : ∀ x : X, Invertible (l : X.residueField x) :=
    sfLocalizationPrimeInvertible k l hl X t
  let : ∀ z : Z, Invertible (l : Z.residueField z) :=
    sfLocalizationPrimeInvertible k l hl Z (i ≫ t)
  let : ∀ u : U, Invertible (l : U.residueField u) :=
    sfLocalizationPrimeInvertible k l hl U (j ≫ t)
  refine ⟨{ stages := S
            supported := A
            closed_pull := ?_
            open_pull := ?_
            comparison := ?_ }⟩
  · exact localizationPullbackEquality i D.closedPull
      (fun E ↦ hgeom.closedPull E) (fun E L h K ↦ hgeom.closedComparison E L h K)
  · exact localizationPullbackEquality j D.openPull
      (fun E ↦ hgeom.openPull E) (fun E L h K ↦ hgeom.openComparison E L h K)
  · intro E
    obtain ⟨hc, ho, hi, hj, he, hca, hoa, hea⟩ := hS E
    exact (stageComparisonOfDescent D hD F R E (S E).supported
      hc ho hi hj he hca hoa hea).some

end WeilConjectures
