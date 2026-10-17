/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.EtaleQcqsFiniteLimits
public import WeilConjectures.AlgebraicTopology.SimplicialObject.CellTower
public import WeilConjectures.AlgebraicTopology.SimplicialObject.MatchingCone

/-!
# Construction of finite split étale hypercovers

Let `X` be a quasi-compact quasi-separated scheme and `Y` a simplicial object of the small
étale site of `X` whose boundaries lift étale locally (`Scheme.Etale.HasLocalLifts`), e.g. the
underlying simplicial object of a split étale hypercover. Given a covering sieve `S m` of
`Y _⦋m⦌` for every `m`, we construct a finite split étale hypercover `V` of `X` together with
a map `V ⟶ Y` such that the nondegenerate `m`-simplices of `V` are a finite coproduct of
pieces mapping into `Y _⦋m⦌` through `S m`.

The construction attaches cells degree by degree (`SimplicialObject.CellTower`): the new
nondegenerate `m`-simplices are finitely many affine étale schemes over the `m`-th matching
object which jointly cover it, and on which the boundary lifts to `Y` through `S m`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial CategoryTheory.SimplicialObject

namespace AlgebraicGeometry

namespace Scheme.Etale

variable {X : Scheme.{u}}

/-- The sieve of local lifts of a boundary cone `p` of degree `m` of `Y`: the maps `g` such
that the precomposition of `p` with `g` is the boundary of an `m`-simplex of `Y`. -/
def liftSieve {Y : SimplicialObject X.Etale} {m : ℕ} {T : X.Etale}
    (p : BoundaryCone Y m T) : Sieve T where
  arrows _ g := ∃ s : _ ⟶ Y _⦋m⦌, BoundaryCone.ofSimplex s = p.precomp g
  downward_closed := by
    rintro _ _ g ⟨s, hs⟩ f
    exact ⟨f ≫ s, by rw [← BoundaryCone.ofSimplex_precomp, hs, BoundaryCone.precomp_precomp]⟩

/-- A simplicial object of the small étale site has local lifts if every boundary lifts to a
simplex étale locally. -/
def HasLocalLifts (Y : SimplicialObject X.Etale) : Prop :=
  ∀ (m : ℕ) (T : X.Etale) (p : BoundaryCone Y m T), liftSieve p ∈ X.smallEtaleTopology T

/-- The matching objects of a simplicial object with qcqs terms are qcqs. -/
lemma isQcqs_matchingObj {W : SimplicialObject X.Etale} (hW : ∀ k, IsQcqs (W.obj k)) :
    ∀ m : ℕ, IsQcqs (matchingObj W m)
  | 0 => isQcqs_of_isLimit _ (limit.isLimit (Functor.empty X.Etale)) (fun j ↦ j.as.elim)
  | 1 => isQcqs_of_isLimit _ (limit.isLimit (Discrete.functor fun _ : Fin 2 ↦ W _⦋0⦌))
      (fun _ ↦ hW _)
  | n + 2 => isQcqs_of_isLimit _ (limit.isLimit (matchingBoundaryIndex W n).multicospan)
      (fun j ↦ match j with
        | .left _ => hW _
        | .right _ => hW _)

end Scheme.Etale

namespace FiniteSplitHypercoverEngine

open Scheme.Etale CellTower

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  {Y : SimplicialObject X.Etale}

/-- The data of a step of the construction: finitely many étale schemes over the matching
object of `W` in degree `m`, together with lifts of the boundary to `Y`. -/
structure StepData (W : SimplicialObject X.Etale) (ℓ : W ⟶ Y) (m : ℕ) where
  /-- The number of pieces. -/
  k : ℕ
  /-- The pieces. -/
  V : Fin k → X.Etale
  /-- The maps to the matching object. -/
  φ : ∀ i, V i ⟶ matchingObj W m
  /-- The lifts to `Y`. -/
  lift : ∀ i, V i ⟶ Y _⦋m⦌
  fac : ∀ i, BoundaryCone.ofSimplex (lift i) = ((matchingObjCone W m).postcomp ℓ).precomp (φ i)

namespace StepData

variable {W : SimplicialObject X.Etale} {ℓ : W ⟶ Y} {m : ℕ}

/-- A step is good if the lifts satisfy the requirement, the pieces are affine and they
jointly cover the matching object. -/
def Good (S : ∀ m : ℕ, Sieve (Y _⦋m⦌)) (d : StepData W ℓ m) : Prop :=
  (∀ i, S m (d.lift i)) ∧ (∀ i, IsAffine (d.V i).left) ∧
    ∀ x : (matchingObj W m).left, ∃ (i : Fin d.k) (y : (d.V i).left), (d.φ i).left y = x

/-- The empty step. -/
def empty : StepData W ℓ m :=
  ⟨0, Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩

/-- The attaching data defined by a step: the new cells are the coproduct of the pieces. -/
def toAttachStep (d : StepData W ℓ m) : AttachStep ℓ m where
  N := ∐ d.V
  cone := (matchingObjCone W m).precomp (Sigma.desc d.φ)
  lift := Sigma.desc d.lift
  fac := by
    refine BoundaryCone.ext' fun Δ h θ ↦ Sigma.hom_ext _ _ fun i ↦ ?_
    have := congrArg (fun c ↦ c.π Δ h θ) (d.fac i)
    simp only [BoundaryCone.postcomp_π, BoundaryCone.precomp_π, BoundaryCone.ofSimplex_π,
      Category.assoc] at this ⊢
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc, this]

end StepData

variable (hY : HasLocalLifts Y) (S : ∀ m : ℕ, Sieve (Y _⦋m⦌))
  (hS : ∀ m, S m ∈ X.smallEtaleTopology (Y _⦋m⦌))

include hY hS in
lemma exists_good (m : ℕ) (W : SimplicialObject X.Etale) (ℓ : W ⟶ Y)
    (hW : ∀ k, IsQcqs (W.obj k)) : ∃ d : StepData W ℓ m, d.Good S := by
  have : CompactSpace (matchingObj W m).left :=
    compactSpace_of_isQcqs (isQcqs_matchingObj hW m)
  let p := (matchingObjCone W m).postcomp ℓ
  let G : Sieve (matchingObj W m) :=
    { arrows := fun _ g ↦ ∃ s : _ ⟶ Y _⦋m⦌, BoundaryCone.ofSimplex s = p.precomp g ∧ S m s
      downward_closed := by
        rintro _ _ g ⟨s, hs, hs'⟩ f
        exact ⟨f ≫ s, by rw [← BoundaryCone.ofSimplex_precomp, hs,
          BoundaryCone.precomp_precomp], (S m).downward_closed hs' f⟩ }
  have hG : G ∈ X.smallEtaleTopology _ := by
    refine GrothendieckTopology.superset_covering _ ?_
      (GrothendieckTopology.bind_covering _ (hY m _ p)
        (R := fun _ g (H : liftSieve p g) ↦ (S m).pullback H.choose)
        (fun _ _ H ↦ GrothendieckTopology.pullback_stable _ _ (hS m)))
    rintro _ _ ⟨_, g', f', H, hg', rfl⟩
    exact ⟨g' ≫ H.choose, by rw [← BoundaryCone.ofSimplex_precomp, H.choose_spec,
      BoundaryCone.precomp_precomp], hg'⟩
  obtain ⟨k, V, φ, hφ, hV, hsurj⟩ := exists_finite_affine_of_mem_smallEtaleTopology G hG
  choose lift hlift using hφ
  exact ⟨⟨k, V, φ, lift, fun i ↦ (hlift i).1⟩, fun i ↦ (hlift i).2, hV, hsurj⟩

/-- The chosen step: a good one if the terms of `W` are qcqs. -/
def chosen (m : ℕ) (W : SimplicialObject X.Etale) (ℓ : W ⟶ Y) : StepData W ℓ m := by
  classical
  exact if h : ∀ k, IsQcqs (W.obj k) then (exists_good hY S hS m W ℓ h).choose else .empty

/-- The attaching steps of the construction. -/
def step (m : ℕ) (W : SimplicialObject X.Etale) (ℓ : W ⟶ Y) : AttachStep ℓ m :=
  (chosen hY S hS m W ℓ).toAttachStep

/-- The step data used in degree `m`. -/
abbrev data (m : ℕ) : StepData (obj (step hY S hS) m) (objToY (step hY S hS) m) m :=
  chosen hY S hS m (obj (step hY S hS) m) (objToY (step hY S hS) m)

lemma cells_eq (m : ℕ) : cells (step hY S hS) m = (data hY S hS m).toAttachStep := rfl

lemma data_good_of_isQcqs (m : ℕ) (h : ∀ k, IsQcqs ((obj (step hY S hS) m).obj k)) :
    (data hY S hS m).Good S := by
  classical
  simp only [data, chosen, dif_pos h]
  exact (exists_good hY S hS m _ _ h).choose_spec

lemma isQcqs_obj : ∀ (m : ℕ) (k : SimplexCategoryᵒᵖ), IsQcqs ((obj (step hY S hS) m).obj k)
  | 0, _ => isQcqs_of_isInitial initialIsInitial
  | m + 1, k => by
    have hgood := data_good_of_isQcqs hY S hS m (isQcqs_obj m)
    have hN : IsQcqs (cells (step hY S hS) m).N := by
      refine isQcqs_of_isColimit_cofan _ (coproductIsCoproduct _) (fun i ↦ ?_)
      have := hgood.2.1 i
      exact isQcqs_of_isAffine _
    exact isQcqs_of_isColimit_binaryCofan _
      ((cells (step hY S hS) m).cone.isColimitAttachBinaryCofan k) (isQcqs_obj m k)
      (isQcqs_of_isColimit_cofan _ (coproductIsCoproduct _) (fun _ ↦ hN))

lemma data_good (m : ℕ) : (data hY S hS m).Good S :=
  data_good_of_isQcqs hY S hS m (isQcqs_obj hY S hS m)

/-- The matching cone of the constructed simplicial object in degree `n`. -/
abbrev cone (n : ℕ) : BoundaryCone (W (step hY S hS)) n (matchingObj (obj (step hY S hS) n) n) :=
  (matchingObjCone (obj (step hY S hS) n) n).postcomp (ι (step hY S hS) n)

lemma isMatchingCone_cone (n : ℕ) : IsMatchingCone _ n (cone hY S hS n) :=
  (isMatchingCone_matchingObjCone _ n).postcomp _
    (fun k hk ↦ isIso_ι_app (step hY S hS) n (op k) hk)

/-- The matching map of the constructed simplicial object in degree `n`. -/
def matchingMap (n : ℕ) :
    (W (step hY S hS)) _⦋n⦌ ⟶ matchingObj (obj (step hY S hS) n) n :=
  (isMatchingCone_cone hY S hS n).lift (BoundaryCone.ofSimplex (𝟙 _))

lemma precomp_matchingMap (n : ℕ) :
    (cone hY S hS n).precomp (matchingMap hY S hS n) = BoundaryCone.ofSimplex (𝟙 _) :=
  (isMatchingCone_cone hY S hS n).precomp_lift _

lemma sigmaDesc_φ_eq (n : ℕ) :
    Sigma.desc (data hY S hS n).φ = cellι (step hY S hS) n ≫ matchingMap hY S hS n := by
  refine (isMatchingCone_cone hY S hS n).hom_ext ?_
  rw [← BoundaryCone.precomp_precomp, precomp_matchingMap, BoundaryCone.ofSimplex_precomp,
    Category.comp_id, ofSimplex_cellι]
  exact (BoundaryCone.precomp_postcomp _ _ _).symm

lemma surjective_matchingMap (n : ℕ) : Surjective (matchingMap hY S hS n).left := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨i, y, hy⟩ := (data_good hY S hS n).2.2 x
  refine ⟨(Sigma.ι (data hY S hS n).V i ≫ cellι (step hY S hS) n).left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← MorphismProperty.Comma.comp_left, Category.assoc,
    ← sigmaDesc_φ_eq, Sigma.ι_desc, hy]

/-- The constructed finite split étale hypercover. -/
def hypercover : FiniteSplitEtaleHypercover X where
  simplicial := W (step hY S hS)
  splitting := splitting (step hY S hS)
  matching n := matchingObj (obj (step hY S hS) n) n
  projection n := (cone hY S hS n).π
  projection_naturality n := (cone hY S hS n).w
  matching_universal n T p hp := by
    let G := Scheme.Etale.forget X
    have h₁ := (isMatchingCone_map_matchingObjCone G (obj (step hY S hS) n) n).postcomp
      (Functor.whiskerRight (ι (step hY S hS) n) G) (fun k hk ↦ by
        have := isIso_ι_app (step hY S hS) n (op k) hk
        exact inferInstanceAs (IsIso (G.map _)))
    obtain ⟨f, hf, huniq⟩ := h₁ T ⟨p, hp⟩
    refine ⟨f, fun Δ h θ ↦ ?_, fun f' hf' ↦ huniq f' ?_⟩
    · have := congrArg (fun c ↦ c.π Δ h θ) hf
      simp only [BoundaryCone.precomp_π, BoundaryCone.postcomp_π, BoundaryCone.map_π,
        Functor.whiskerRight_app] at this
      rw [← this, BoundaryCone.postcomp_π, G.map_comp]
    · refine BoundaryCone.ext' fun Δ h θ ↦ ?_
      simp only [BoundaryCone.precomp_π, BoundaryCone.postcomp_π, BoundaryCone.map_π,
        Functor.whiskerRight_app]
      rw [← hf' Δ h θ, BoundaryCone.postcomp_π, G.map_comp]
  matchingMap := matchingMap hY S hS
  matchingMap_projection n Δ h θ := by
    have := congrArg (fun c ↦ c.π Δ h θ) (precomp_matchingMap hY S hS n)
    simpa using this
  matching_cover := surjective_matchingMap hY S hS
  finite_each_degree n := by
    have hgood := data_good hY S hS n
    refine ⟨(data hY S hS n).k, (data hY S hS n).V, Sigma.ι _,
      ⟨coproductIsCoproduct _⟩, fun i ↦ ?_⟩
    have := hgood.2.1 i
    have h := isQcqs_of_isAffine ((data hY S hS n).V i)
    exact ⟨inferInstance, inferInstance, inferInstance, h.1, h.2⟩

/-- The map from the constructed hypercover to `Y`. -/
def hypercoverToY : (hypercover hY S hS).simplicial ⟶ Y := toY (step hY S hS)

include hY hS in
/-- Blueprint `lem-weil-pbc-hypercover-refinement`: a simplicial object with local lifts is
refined by a finite split étale hypercover whose nondegenerate pieces satisfy prescribed
local requirements. -/
theorem exists_hypercover :
    ∃ (V : FiniteSplitEtaleHypercover X) (ℓ : V.simplicial ⟶ Y), ∀ m : ℕ,
      ∃ (k : ℕ) (P : Fin k → X.Etale) (ι : ∀ i, P i ⟶ V.splitting.N m),
        Nonempty (IsColimit (Cofan.mk _ ι)) ∧
          ∀ i, S m (ι i ≫ V.splitting.ι m ≫ ℓ.app _) := by
  refine ⟨hypercover hY S hS, hypercoverToY hY S hS, fun m ↦ ⟨(data hY S hS m).k,
    (data hY S hS m).V, Sigma.ι _, ⟨coproductIsCoproduct _⟩, fun i ↦ ?_⟩⟩
  have h : Sigma.ι (data hY S hS m).V i ≫ (hypercover hY S hS).splitting.ι m ≫
      (hypercoverToY hY S hS).app _ = (data hY S hS m).lift i := by
    change Sigma.ι _ i ≫ cellι (step hY S hS) m ≫ (toY (step hY S hS)).app _ = _
    rw [cellι_toY_app]
    exact Sigma.ι_desc _ _
  rw [h]
  exact (data_good hY S hS m).1 i

end FiniteSplitHypercoverEngine

end AlgebraicGeometry
