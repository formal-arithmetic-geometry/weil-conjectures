/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHypercover

/-!
# Refining étale hypercovers by qcqs hypercovers

Let `X` be a quasi-compact quasi-separated scheme. We show that every semi-simplicial hypercover
`U` of the small étale site of `X` is refined by a qcqs hypercover, i.e. a hypercover all of
whose terms are quasi-compact and quasi-separated
(`AlgebraicGeometry.Scheme.exists_isQcqsHypercover_hom`, blueprint
`lem-weil-pbc-hypercover-refinement`).

The construction is a variant of the relative coskeleton of
`CategoryTheory.SemiSimplicialObject.refinement`, in which the new simplices are chosen at each
stage instead of being given in advance. Inductively,

* `V₀ ⟶ U₀` is chosen such that `V₀` covers the terminal object, and
* `V_{n + 1} ⟶ M_{n + 1}(V) ×_{M_{n + 1}(U)} U_{n + 1}` is chosen such that the composition
  `V_{n + 1} ⟶ M_{n + 1}(V)` is a covering.

This works in any site `(C, J)` with finite limits, for a property `P` of objects which is stable
under finite limits and such that every covering `A ⟶ M` with `P M` is refined by a covering
`Q ⟶ A ⟶ M` with `P Q` (`CategoryTheory.SemiSimplicialObject.IsHypercover.exists_hom_of_prop`):
since the matching maps of `U` are coverings, so are their pullbacks
`M_{n + 1}(V) ×_{M_{n + 1}(U)} U_{n + 1} ⟶ M_{n + 1}(V)`, and `M_{n + 1}(V)` satisfies `P` as a
finite limit of terms of `V`. For the étale site and the property of being quasi-compact and
quasi-separated, the refinement step takes a finite disjoint union of affine étale schemes over
`A` whose images cover the quasi-compact `M`
(`AlgebraicGeometry.Scheme.exists_etaleQcqs_ofArrows_comp_mem`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.SemiSimplicialObject

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

omit [HasFiniteLimits C] in
/-- The pullback of a morphism generating a covering sieve generates a covering sieve. -/
lemma ofArrows_pullback_fst_mem [HasPullbacks C] {J : GrothendieckTopology C} {Y Z W : C}
    (f : Y ⟶ Z) {g : W ⟶ Z} (hg : Sieve.ofArrows (fun _ : Unit ↦ W) (fun _ ↦ g) ∈ J Z) :
    Sieve.ofArrows (fun _ : Unit ↦ pullback f g) (fun _ ↦ pullback.fst f g) ∈ J Y := by
  refine J.superset_covering (fun T h hh ↦ ?_) (J.pullback_stable f hg)
  rw [Sieve.pullback_apply, Sieve.mem_ofArrows_iff] at hh
  obtain ⟨_, a, ha⟩ := hh
  exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨(), pullback.lift h a ha, (pullback.lift_fst _ _ _).symm⟩

namespace Refinement

variable (U : SemiSimplicialObject C) (r : ∀ {A M : C}, (A ⟶ M) → Over A)

/-- The stages of a refinement of `U` whose new simplices map directly to the simplices of `U`. -/
abbrev SelfStage (n : ℕ) : Type _ :=
  Stage U U.obj (fun k ↦ 𝟙 (U.obj k)) n

namespace Stage

variable {U} {n : ℕ} (s : SelfStage U n)

/-- The projection `M_{n + 2}(V) ×_{M_{n + 2}(U)} U_{n + 2} ⟶ M_{n + 2}(V)`. -/
noncomputable abbrev matchingPullbackFst :
    pullback s.toMatchingU (U.toMatching (n + 1)) ⟶ s.matching :=
  pullback.fst _ _

/-- The next stage, with `V_{n + 2}` chosen by `r` over
`M_{n + 2}(V) ×_{M_{n + 2}(U)} U_{n + 2}`. -/
noncomputable def nextBy : SelfStage U (n + 1) where
  A := s.B
  B := (r s.matchingPullbackFst).left
  d i := (r s.matchingPullbackFst).hom ≫ pullback.fst _ _ ≫ s.matchingπ i
  fA := s.fB
  fB := (r s.matchingPullbackFst).hom ≫ pullback.snd _ _
  comm i := by
    have := pullback.condition (f := s.toMatchingU) (g := U.toMatching (n + 1)) =≫
      U.matchingπ (n + 1) i
    simp only [Category.assoc, toMatchingU_π, toMatching_π] at this
    simp only [Category.assoc, this]
  ρA := s.fB
  ρA_π := Category.comp_id _
  ρB := (r s.matchingPullbackFst).hom ≫ pullback.snd _ _
  ρB_π := Category.comp_id _

lemma nextBy_d_comp_d {i j : Fin (n + 2)} (h : i ≤ j) :
    (s.nextBy r).d j.succ ≫ s.d i = (s.nextBy r).d i.castSucc ≫ s.d j := by
  simp only [nextBy, Category.assoc, s.matchingπ_comp_d h]

end Stage

/-- The chosen `0`-simplices `V₀ ⟶ U₀`. -/
noncomputable def zeroSimplices : Over (U.obj 0) :=
  r (terminalIsTerminal.from (U.obj 0))

/-- The map `V₀ × V₀ ⟶ M₁(U)`. -/
noncomputable def zeroToMatching :
    ∏ᶜ (fun _ : Fin 2 ↦ (zeroSimplices U r).left) ⟶ U.matching 0 :=
  U.matchingLift (fun i ↦ Pi.π _ i ≫ (zeroSimplices U r).hom) (U.compatible_zero _)

@[reassoc (attr := simp)]
lemma zeroToMatching_π (i : Fin 2) :
    zeroToMatching U r ≫ U.matchingπ 0 i = Pi.π _ i ≫ (zeroSimplices U r).hom := by
  simp [zeroToMatching]

/-- The stage `0`: `V₀` is given by `zeroSimplices`, and `V₁` is chosen by `r` over
`(V₀ × V₀) ×_{M₁(U)} U₁`. -/
noncomputable def stageZeroBy : SelfStage U 0 where
  A := (zeroSimplices U r).left
  B := (r (pullback.fst (zeroToMatching U r) (U.toMatching 0))).left
  d i := (r (pullback.fst (zeroToMatching U r) (U.toMatching 0))).hom ≫ pullback.fst _ _ ≫
    Pi.π _ i
  fA := (zeroSimplices U r).hom
  fB := (r (pullback.fst (zeroToMatching U r) (U.toMatching 0))).hom ≫ pullback.snd _ _
  comm i := by
    have := pullback.condition (f := zeroToMatching U r) (g := U.toMatching 0) =≫
      U.matchingπ 0 i
    simp only [Category.assoc, zeroToMatching_π, toMatching_π] at this
    simp only [Category.assoc, this]
  ρA := (zeroSimplices U r).hom
  ρA_π := Category.comp_id _
  ρB := (r (pullback.fst (zeroToMatching U r) (U.toMatching 0))).hom ≫ pullback.snd _ _
  ρB_π := Category.comp_id _

/-- The stages of the refinement with chosen simplices. -/
noncomputable def stageBy : (n : ℕ) → SelfStage U n
  | 0 => stageZeroBy U r
  | n + 1 => (stageBy n).nextBy r

end Refinement

open Refinement

variable (U : SemiSimplicialObject C) (r : ∀ {A M : C}, (A ⟶ M) → Over A)

/-- The refinement of `U` with simplices chosen by `r`: `V₀ = r(U₀ ⟶ ⊤)` and
`V_{n + 1} = r(M_{n + 1}(V) ×_{M_{n + 1}(U)} U_{n + 1} ⟶ M_{n + 1}(V))`. -/
noncomputable def refinementBy : SemiSimplicialObject C where
  obj n := (stageBy U r n).A
  δ n i := (stageBy U r n).d i
  δ_comp_δ n _ _ h := (stageBy U r n).nextBy_d_comp_d r h

/-- The morphism from the refinement with chosen simplices. -/
noncomputable def refinementByHom : refinementBy U r ⟶ U where
  app n := (stageBy U r n).fA
  app_δ n i := ((stageBy U r n).comm i).symm

/-- The hypothesis on the choice function `r`: it refines every covering `p : A ⟶ M` with `P M`
by a covering `(r p).left ⟶ A ⟶ M` with `P (r p).left`. -/
def IsGoodChoice (P : ObjectProperty C) (J : GrothendieckTopology C)
    (r : ∀ {A M : C}, (A ⟶ M) → Over A) : Prop :=
  ∀ ⦃A M : C⦄ (p : A ⟶ M), P M → Sieve.ofArrows (fun _ : Unit ↦ A) (fun _ ↦ p) ∈ J M →
    P (r p).left ∧ Sieve.ofArrows (fun _ : Unit ↦ (r p).left) (fun _ ↦ (r p).hom ≫ p) ∈ J M

section Choice

variable {U r} {J : GrothendieckTopology C} (P : ObjectProperty C)
  [P.IsClosedUnderFiniteProducts] [P.IsClosedUnderLimitsOfShape WalkingParallelPair]

omit [P.IsClosedUnderLimitsOfShape WalkingParallelPair] in
lemma prop_zeroSimplices (hU : U.IsHypercover J) (hr : IsGoodChoice P J r) :
    P (zeroSimplices U r).left ∧
      Sieve.ofArrows (fun _ : Unit ↦ (zeroSimplices U r).left)
        (fun _ ↦ (zeroSimplices U r).hom ≫ terminalIsTerminal.from (U.obj 0)) ∈ J (⊤_ C) :=
  hr _ P.prop_terminal ((U.isHypercover_iff J terminalIsTerminal).1 hU).1

omit [P.IsClosedUnderLimitsOfShape WalkingParallelPair] in
lemma prop_stageZeroBy_B (hU : U.IsHypercover J) (hr : IsGoodChoice P J r) :
    P (stageZeroBy U r).B ∧
      Sieve.ofArrows (fun _ : Unit ↦ (stageZeroBy U r).B)
        (fun _ ↦ (r (pullback.fst (zeroToMatching U r) (U.toMatching 0))).hom ≫
          pullback.fst _ _) ∈ J (∏ᶜ (fun _ : Fin 2 ↦ (zeroSimplices U r).left)) :=
  hr _ (P.prop_product fun _ ↦ (prop_zeroSimplices P hU hr).1)
    (ofArrows_pullback_fst_mem _ (((U.isHypercover_iff J terminalIsTerminal).1 hU).2 0))

lemma Refinement.Stage.prop_matching {n : ℕ} (s : SelfStage U n) (hA : P s.A) (hB : P s.B) :
    P s.matching := by
  refine P.prop_limit _ fun j ↦ ?_
  cases j
  · exact P.prop_product fun _ ↦ hB
  · exact P.prop_product fun _ ↦ hA

lemma Refinement.Stage.prop_nextBy (hU : U.IsHypercover J) (hr : IsGoodChoice P J r) {n : ℕ}
    (s : SelfStage U n) (hA : P s.A) (hB : P s.B) :
    P (s.nextBy r).B ∧
      Sieve.ofArrows (fun _ : Unit ↦ (s.nextBy r).B)
        (fun _ ↦ (r s.matchingPullbackFst).hom ≫ s.matchingPullbackFst) ∈ J s.matching :=
  hr _ (s.prop_matching P hA hB)
    (ofArrows_pullback_fst_mem _ (((U.isHypercover_iff J terminalIsTerminal).1 hU).2 (n + 1)))

lemma prop_stageBy (hU : U.IsHypercover J) (hr : IsGoodChoice P J r) (n : ℕ) :
    P (stageBy U r n).A ∧ P (stageBy U r n).B := by
  induction n with
  | zero => exact ⟨(prop_zeroSimplices P hU hr).1, (prop_stageZeroBy_B P hU hr).1⟩
  | succ n ih => exact ⟨ih.2, ((stageBy U r n).prop_nextBy P hU hr ih.1 ih.2).1⟩

/-- The refinement with chosen simplices of a hypercover is a hypercover, provided the choices
are good. -/
lemma IsHypercover.refinementBy (hU : U.IsHypercover J) (hr : IsGoodChoice P J r) :
    (refinementBy U r).IsHypercover J where
  coverSieve_mem T := by
    refine J.superset_covering ?_
      (exists_lift_mem (prop_zeroSimplices P hU hr).2 (terminalIsTerminal.from T))
    rintro T' g ⟨l, -⟩
    exact ⟨l⟩
  liftSieve_mem {n} T x hx := by
    cases n with
    | zero =>
      refine J.superset_covering ?_
        (exists_lift_mem (prop_stageZeroBy_B P hU hr).2 (Pi.lift x))
      rintro T' g ⟨l, hl⟩
      refine ⟨l, fun i ↦ ?_⟩
      have := hl =≫ Pi.π _ i
      simp only [Category.assoc, Pi.lift_π] at this
      exact this
    | succ m =>
      have h := (stageBy U r m).prop_nextBy P hU hr (prop_stageBy P hU hr m).1
        (prop_stageBy P hU hr m).2
      refine J.superset_covering ?_ (exists_lift_mem h.2 ((stageBy U r m).matchingLift x hx))
      rintro T' g ⟨l, hl⟩
      refine ⟨l, fun i ↦ ?_⟩
      have := hl =≫ (stageBy U r m).matchingπ i
      simp only [Category.assoc, Stage.matchingLift_π] at this
      exact this

variable {P} in
/-- **Refinement of hypercovers within a class of objects.** Let `P` be a property of objects of
a site `(C, J)` with finite limits, stable under finite limits, such that every covering
`p : A ⟶ M` with `P M` is refined by a covering `Q ⟶ A ⟶ M` with `P Q`. Then every hypercover
`U` is refined by a hypercover all of whose terms satisfy `P`. -/
theorem IsHypercover.exists_hom_of_prop [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
    {U : SemiSimplicialObject C} (hU : U.IsHypercover J)
    (hP : ∀ ⦃A M : C⦄ (p : A ⟶ M), P M → Sieve.ofArrows (fun _ : Unit ↦ A) (fun _ ↦ p) ∈ J M →
      ∃ (Q : C) (q : Q ⟶ A), P Q ∧ Sieve.ofArrows (fun _ : Unit ↦ Q) (fun _ ↦ q ≫ p) ∈ J M) :
    ∃ V : SemiSimplicialObject C, V.IsHypercover J ∧ (∀ n, P (V.obj n)) ∧ Nonempty (V ⟶ U) := by
  classical
  let r : ∀ {A M : C}, (A ⟶ M) → Over A := fun {A M} p ↦
    if h : P M ∧ Sieve.ofArrows (fun _ : Unit ↦ A) (fun _ ↦ p) ∈ J M then
      Over.mk (hP p h.1 h.2).choose_spec.choose
    else Over.mk (𝟙 A)
  have hr : IsGoodChoice P J r := by
    intro A M p hM hp
    dsimp only [r]
    rw [dif_pos ⟨hM, hp⟩]
    exact (hP p hM hp).choose_spec.choose_spec
  exact ⟨SemiSimplicialObject.refinementBy U r, hU.refinementBy P hr,
    fun n ↦ (prop_stageBy P hU hr n).1, ⟨refinementByHom U r⟩⟩

end Choice

end CategoryTheory.SemiSimplicialObject

namespace AlgebraicGeometry.Scheme

open CategoryTheory.SemiSimplicialObject

variable {X : Scheme.{u}}

/-- A covering `p : A ⟶ M` of the small étale site of `X` with `M` quasi-compact is refined by a
covering `Q ⟶ A ⟶ M` with `Q` quasi-compact and quasi-separated: a finite disjoint union of
affine étale schemes over `A` whose images cover `M`. -/
lemma exists_etaleQcqs_ofArrows_comp_mem {A M : X.Etale} [CompactSpace M.left] (p : A ⟶ M)
    (hp : Sieve.ofArrows (fun _ : Unit ↦ A) (fun _ ↦ p) ∈ X.smallEtaleTopology M) :
    ∃ (Q : X.Etale) (q : Q ⟶ A), etaleQcqs X Q ∧
      Sieve.ofArrows (fun _ : Unit ↦ Q) (fun _ ↦ q ≫ p) ∈ X.smallEtaleTopology M := by
  obtain ⟨n, U, g, hg, hU, hcov⟩ := exists_finite_affine_of_mem_smallEtaleTopology hp
  choose _ t ht using fun a ↦ (Sieve.mem_ofArrows_iff _ _ _).1 (hg a)
  have : Etale (Sigma.desc fun a ↦ (U a).hom) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @AlgebraicGeometry.Etale) fun a ↦ (U a).prop
  let W : X.Etale := Etale.mk (Sigma.desc fun a ↦ (U a).hom)
  let ι (a : Fin n) : U a ⟶ W :=
    MorphismProperty.Over.homMk (Sigma.ι (fun a ↦ (U a).left) a) (by simp [W])
  let q : W ⟶ A := MorphismProperty.Over.homMk (Sigma.desc fun a ↦ (t a).left)
    (Sigma.hom_ext _ _ fun a ↦ by simp [W])
  have hιq (a : Fin n) : ι a ≫ q ≫ p = g a := by
    rw [ht a, ← Category.assoc]
    exact congrArg (· ≫ p) (MorphismProperty.Over.Hom.ext (Sigma.ι_desc _ a))
  have : IsAffine W.left := inferInstanceAs (IsAffine (∐ fun a ↦ (U a).left))
  refine ⟨W, q, ⟨inferInstance, inferInstance⟩, ?_⟩
  refine (ofArrows_mem_smallEtaleTopology_iff _).2 (Set.eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨_, ⟨a, rfl⟩, y, rfl⟩ := hcov.symm ▸ Set.mem_univ x
  refine Set.mem_iUnion.2 ⟨⟨⟩, (ι a).left y, ?_⟩
  rw [← hιq a]
  rfl

/-- **Refinement by qcqs hypercovers** (blueprint `lem-weil-pbc-hypercover-refinement`): every
étale hypercover `U` of a quasi-compact quasi-separated scheme `X` is refined by a hypercover with
quasi-compact quasi-separated terms. The refinement `V` is built inductively: `V₀` is a finite
disjoint union of affine étale schemes over `U₀` covering `X`, and `V_{n + 1}` is a finite
disjoint union of affine étale schemes over `M_{n + 1}(V) ×_{M_{n + 1}(U)} U_{n + 1}` covering the
matching object `M_{n + 1}(V)`, which is quasi-compact and quasi-separated as a finite limit of
quasi-compact quasi-separated schemes over the qcqs `X`. -/
theorem exists_isQcqsHypercover_hom [CompactSpace X] [QuasiSeparatedSpace X]
    {U : SemiSimplicialObject X.Etale} (hU : U.IsHypercover X.smallEtaleTopology) :
    ∃ V : SemiSimplicialObject X.Etale, IsQcqsHypercover V ∧ Nonempty (V ⟶ U) := by
  obtain ⟨V, hV, hP, f⟩ := hU.exists_hom_of_prop (P := etaleQcqs X) fun A M p hM hp ↦ by
    have := hM.1
    exact exists_etaleQcqs_ofArrows_comp_mem p hp
  exact ⟨V, ⟨hV, fun n ↦ (hP n).1, fun n ↦ (hP n).2⟩, f⟩

end AlgebraicGeometry.Scheme
