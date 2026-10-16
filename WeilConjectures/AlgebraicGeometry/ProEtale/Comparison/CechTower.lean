/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.CategoryTheory.Sites.IsCechNerveAt

/-!
# The Čech nerve of a morphism of the affine pro-étale site as a limit

Let `q : W ⟶ U₀` be a morphism of the small affine pro-étale site of a scheme `S`, presented as
a morphism of relative limit presentations by affine étale `S`-schemes. We construct the tower
of iterated fibre products `W ×_{U₀} ⋯ ×_{U₀} W`, together with relative limit presentations
whose stages are the iterated fibre products of the étale stages
(`AlgebraicGeometry.Scheme.AffineProEt.cechTower`). This identifies the Čech nerve of `q` with
the limit of the Čech nerves of the étale stages, compatibly with the face maps
(`AlgebraicGeometry.Scheme.AffineProEt.CechTower.map_faceHom_map`).

We also show that the objects of the Čech nerve of `q` in the pro-étale site are
pro-affine-étale (`AlgebraicGeometry.Scheme.AffineProEt.proAffineEtale_cechNerve_hom`), and that
a surjection of the affine pro-étale site generates a covering sieve of the pro-étale site.

This is a port of part of `Proetale/Topology/Comparison/CechColimit.lean` and
`Proetale/Topology/Comparison/Acyclicity.lean` of the `proetale` package.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped Simplicial

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}


namespace AffineProEt

/-- Regard a pro-étale object with pro-affine-étale structure morphism as an object of the
affine pro-étale site. -/
def ofProEt (X : S.ProEt) (hX : proAffineEtale X.hom) : S.AffineProEt :=
  AffineProEt.mk X.hom hX

lemma toProEt_obj_ofProEt (X : S.ProEt) (hX : proAffineEtale X.hom) :
    (AffineProEt.toProEt S).obj (ofProEt X hX) = X :=
  rfl

/-- A surjective morphism in the affine pro-étale site generates a covering sieve of the
pro-étale topology. -/
lemma generate_singleton_toProEt_map_mem {W U₀ : S.AffineProEt} (q : W ⟶ U₀)
    (hq : Surjective q.left) :
    Sieve.generate (Presieve.singleton ((AffineProEt.toProEt S).map q)) ∈
      ProEt.topology S ((AffineProEt.toProEt S).obj U₀) := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  simp only [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_singleton,
    AffineProEt.toProEt_map,
    Functor.comp_map, ProEt.forget_map, Over.forget_map]
  have : Surjective q.left := hq
  exact q.left.singleton_mem_propQCPrecoverage inferInstance

/-- The structure morphism of the `(n+1)`-fold fibre product of `W` over `U₀` in the
pro-étale site is pro-affine-étale, by induction on `n` using closure of pro-affine-étale
structure maps under binary pullbacks. -/
lemma proAffineEtale_widePullback_hom {W U₀ : S.AffineProEt} (q : W ⟶ U₀) (n : ℕ) :
    proAffineEtale (widePullback ((AffineProEt.toProEt S).obj U₀)
      (fun _ : Fin (n + 1) ↦ (AffineProEt.toProEt S).obj W)
      (fun _ ↦ (AffineProEt.toProEt S).map q)).hom := by
  induction n with
  | zero =>
    -- The unary wide pullback is isomorphic to `W` via the projection.
    set g := (AffineProEt.toProEt S).map q
    let l : (AffineProEt.toProEt S).obj W ⟶
        widePullback ((AffineProEt.toProEt S).obj U₀)
          (fun _ : Fin 1 ↦ (AffineProEt.toProEt S).obj W) (fun _ ↦ g) :=
      WidePullback.lift g (fun _ ↦ 𝟙 _) (fun _ ↦ Category.id_comp g)
    have h1 : WidePullback.π (fun _ : Fin 1 ↦ g) 0 ≫ l = 𝟙 _ := by
      apply WidePullback.hom_ext
      · intro i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, WidePullback.lift_base, WidePullback.π_arrow, Category.id_comp]
    have h2 : l ≫ WidePullback.π (fun _ : Fin 1 ↦ g) 0 = 𝟙 _ :=
      WidePullback.lift_π _ _ _ _ 0
    have : IsIso (WidePullback.π (fun _ : Fin 1 ↦ g) 0) := ⟨l, h1, h2⟩
    have : IsIso (WidePullback.π (fun _ : Fin 1 ↦ g) 0).left :=
      inferInstanceAs (IsIso ((ProEt.forget S ⋙ Over.forget S).map
        (WidePullback.π (fun _ : Fin 1 ↦ g) 0)))
    have hw : (WidePullback.π (fun _ : Fin 1 ↦ g) 0).left ≫
        ((AffineProEt.toProEt S).obj W).hom =
          (widePullback ((AffineProEt.toProEt S).obj U₀)
            (fun _ : Fin 1 ↦ (AffineProEt.toProEt S).obj W) (fun _ ↦ g)).hom :=
      MorphismProperty.Over.w _
    rw [← hw]
    exact (MorphismProperty.cancel_left_of_respectsIso proAffineEtale _ _).mpr W.prop
  | succ n ih =>
    set g := (AffineProEt.toProEt S).map q
    -- The restriction morphism forgetting the first coordinate.
    let r : widePullback ((AffineProEt.toProEt S).obj U₀)
          (fun _ : Fin (n + 2) ↦ (AffineProEt.toProEt S).obj W) (fun _ ↦ g) ⟶
        widePullback ((AffineProEt.toProEt S).obj U₀)
          (fun _ : Fin (n + 1) ↦ (AffineProEt.toProEt S).obj W) (fun _ ↦ g) :=
      WidePullback.lift (WidePullback.base _)
        (fun i ↦ WidePullback.π _ i.succ) (fun i ↦ WidePullback.π_arrow _ _)
    have hsq : WidePullback.π (fun _ : Fin (n + 2) ↦ g) 0 ≫ g =
        r ≫ WidePullback.base _ := by
      rw [WidePullback.π_arrow, WidePullback.lift_base]
    -- The `(n+2)`-fold fibre product is the binary pullback of the `(n+1)`-fold one with `W`.
    have hpb : IsPullback (WidePullback.π (fun _ : Fin (n + 2) ↦ g) 0) r g
        (WidePullback.base _) := by
      refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq
        (fun s ↦ WidePullback.lift (s.snd ≫ WidePullback.base _)
          (fun i ↦ Fin.cases s.fst (fun i' ↦ s.snd ≫ WidePullback.π _ i') i) ?_)
        (fun s ↦ ?_) (fun s ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_))
      · intro i
        induction i using Fin.cases with
        | zero => simpa using s.condition
        | succ i' => simp only [Fin.cases_succ, Category.assoc, WidePullback.π_arrow]
      · simp only [WidePullback.lift_π, Fin.cases_zero]
      · apply WidePullback.hom_ext
        · intro i
          rw [Category.assoc,
            show r ≫ WidePullback.π _ i = WidePullback.π _ i.succ from
              WidePullback.lift_π _ _ _ _ i,
            WidePullback.lift_π]
          simp
        · rw [Category.assoc,
            show r ≫ WidePullback.base _ = WidePullback.base _ from
              WidePullback.lift_base _ _ _ _,
            WidePullback.lift_base]
      · apply WidePullback.hom_ext
        · intro i
          rw [WidePullback.lift_π]
          induction i using Fin.cases with
          | zero => simpa using hm₁
          | succ i' =>
            have h3 : m ≫ WidePullback.π _ i'.succ = m ≫ r ≫ WidePullback.π _ i' := by
              rw [show r ≫ WidePullback.π _ i' = WidePullback.π _ i'.succ from
                WidePullback.lift_π _ _ _ _ i']
            rw [h3, ← Category.assoc, hm₂]
            simp
        · rw [WidePullback.lift_base]
          have h3 : m ≫ WidePullback.base _ = m ≫ r ≫ WidePullback.base _ := by
            rw [show r ≫ WidePullback.base _ = WidePullback.base _ from
              WidePullback.lift_base _ _ _ _]
          rw [h3, ← Category.assoc, hm₂]
    -- Transfer to `Over S` and apply closure of pro-affine-étale structure maps
    -- under pullbacks.
    have hpbO := hpb.map (ProEt.forget S)
    refine ObjectProperty.prop_of_isLimit (P := proAffineEtale.overObj (X := S))
      hpbO.isLimit ?_
    rintro (_ | _ | _)
    · exact U₀.prop
    · exact W.prop
    · exact ih

/-- **(D2)** The Čech nerve of a morphism of affine pro-étale objects consists of objects
with pro-affine-étale structure morphism. -/
lemma proAffineEtale_cechNerve_hom {W U₀ : S.AffineProEt} (q : W ⟶ U₀) (n : ℕ) :
    proAffineEtale
      ((Arrow.mk ((AffineProEt.toProEt S).map q)).cechNerve.obj (op ⦋n⦌)).hom :=
  proAffineEtale_widePullback_hom q n


end AffineProEt

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.AffineProEt

/-! ### The tower of iterated fibre products

We construct, for a morphism `q : W ⟶ U₀` of affine pro-étale objects presented as a
morphism of relative limit presentations, the tower of iterated fibre products of `W`
over `U₀`, simultaneously with relative limit presentations whose stages carry étale
Čech nerve data and with pro-étale Čech nerve data on the total spaces. -/

variable {S : Scheme.{u}}

section Tower

variable {W U₀ : S.AffineProEt} (q : W ⟶ U₀)
variable {A : Type u} [SmallCategory A]
variable (presU : RelativeLimitPresentation A (AffineEtale.toAffineProEt S) U₀)
variable (presW : RelativeLimitPresentation A (AffineEtale.toAffineProEt S) W)
variable (fW : presW.Hom presU)

/-- The `n`-th level of the tower of iterated fibre products of `q : W ⟶ U₀`: an affine
pro-étale object `M` with a relative limit presentation whose stages carry Čech nerve
data for the étale level maps, and which itself carries Čech nerve data for `q` on the
pro-étale site. -/
structure CechTower (n : ℕ) where
  /-- The `n`-th iterated fibre product of `W` over `U₀`. -/
  M : S.AffineProEt
  /-- The relative limit presentation of `M`. -/
  presM : RelativeLimitPresentation A (AffineEtale.toAffineProEt S) M
  /-- The base morphism of presentations. -/
  bM : presM.Hom presU
  /-- The projections of `M` to `W`. -/
  πM : Fin (n + 1) → (M ⟶ W)
  /-- The stage-wise projections to the stages of `W`. -/
  πSt : ∀ a : A, Fin (n + 1) → (presM.diag.obj a ⟶ presW.diag.obj a)
  πM_π : ∀ (j : Fin (n + 1)) (a : A), πM j ≫ presW.π.app a =
    presM.π.app a ≫ (AffineEtale.toAffineProEt S).map (πSt a j)
  πSt_nat : ∀ {a a' : A} (u : a ⟶ a') (j : Fin (n + 1)),
    presM.diag.map u ≫ πSt a' j = πSt a j ≫ presW.diag.map u
  /-- The Čech nerve data at the étale stages. -/
  ét : ∀ a : A, IsCechNerveAt ((AffineEtale.Spec S).map (fW.natTrans.app a)) n
    ((AffineEtale.Spec S).obj (presM.diag.obj a))
  ét_π : ∀ (a : A) (j : Fin (n + 1)), (ét a).π j = (AffineEtale.Spec S).map (πSt a j)
  ét_base : ∀ a : A, (ét a).base = (AffineEtale.Spec S).map (bM.natTrans.app a)
  /-- The Čech nerve data on the pro-étale site. -/
  pro : IsCechNerveAt ((AffineProEt.toProEt S).map q) n ((AffineProEt.toProEt S).obj M)
  pro_π : ∀ j : Fin (n + 1), pro.π j = (AffineProEt.toProEt S).map (πM j)
  pro_base : pro.base = (AffineProEt.toProEt S).map bM.map

namespace CechTower

variable {q presU presW fW}

/-- The zeroth level of the tower: `W` itself. -/
noncomputable def zero (hfW : fW.map = q) : CechTower q presU presW fW 0 where
  M := W
  presM := presW
  bM := fW
  πM _ := 𝟙 W
  πSt _ _ := 𝟙 _
  πM_π _ _ := by
    simp only [Category.id_comp, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  πSt_nat _ _ := by simp
  ét _ := .zero _
  ét_π _ _ := by rw [IsCechNerveAt.zero_π, CategoryTheory.Functor.map_id]
  ét_base _ := rfl
  pro := .zero _
  pro_π _ := by rw [IsCechNerveAt.zero_π, CategoryTheory.Functor.map_id]
  pro_base := by rw [IsCechNerveAt.zero_base, hfW]

variable {n : ℕ}

/-- The presentation of the next level of the tower, by stage-wise pullbacks. -/
noncomputable def presNext (T : CechTower q presU presW fW n) (hfW : fW.map = q) :
    RelativeLimitPresentation A (AffineEtale.toAffineProEt S) (pullback T.bM.map q) :=
  RelativeLimitPresentation.pullback (F := AffineEtale.toAffineProEt S) T.bM.map q
    (IsPullback.of_hasPullback T.bM.map q).cone (IsPullback.of_hasPullback T.bM.map q).isLimit
    T.presM presW presU T.bM fW rfl hfW

variable (T : CechTower q presU presW fW n) (hfW : fW.map = q)

lemma presNext_π_app_fst (a : A) :
    (T.presNext hfW).π.app a ≫ (AffineEtale.toAffineProEt S).map
        (pullback.fst (T.bM.natTrans.app a) (fW.natTrans.app a)) =
      pullback.fst T.bM.map q ≫ T.presM.π.app a :=
  IsPullback.lift_fst _ _ _ _

lemma presNext_π_app_snd (a : A) :
    (T.presNext hfW).π.app a ≫ (AffineEtale.toAffineProEt S).map
        (pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a)) =
      pullback.snd T.bM.map q ≫ presW.π.app a :=
  IsPullback.lift_snd _ _ _ _

lemma presNext_diag_map {a a' : A} (u : a ⟶ a') :
    (T.presNext hfW).diag.map u =
      pullback.map (T.bM.natTrans.app a) (fW.natTrans.app a) (T.bM.natTrans.app a')
        (fW.natTrans.app a') (T.presM.diag.map u) (presW.diag.map u) (presU.diag.map u)
        (by simp) (by simp) :=
  rfl

/-- The base morphism of presentations of the next level. -/
noncomputable def bMNext : (T.presNext hfW).Hom presU where
  natTrans :=
    { app a := pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a) ≫ fW.natTrans.app a
      naturality a a' u := by
        rw [presNext_diag_map]
        rw [pullback.lift_snd_assoc, Category.assoc, fW.natTrans.naturality,
          Category.assoc] }

@[simp]
lemma bMNext_app (a : A) :
    (T.bMNext hfW).natTrans.app a =
      pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a) ≫ fW.natTrans.app a :=
  rfl

lemma bMNext_map : (T.bMNext hfW).map = pullback.snd T.bM.map q ≫ q := by
  apply presU.isLimit.hom_ext
  intro a
  rw [RelativeLimitPresentation.Hom.map_π, bMNext_app, Functor.map_comp, ← Category.assoc,
    presNext_π_app_snd, Category.assoc, ← RelativeLimitPresentation.Hom.map_π fW a, hfW,
    Category.assoc]

/-- The projections of the next level of the tower. -/
noncomputable def πMNext : Fin (n + 2) → (pullback T.bM.map q ⟶ W) :=
  Fin.snoc (fun j ↦ pullback.fst T.bM.map q ≫ T.πM j) (pullback.snd T.bM.map q)

/-- The stage-wise projections of the next level of the tower. -/
noncomputable def πStNext (a : A) :
    Fin (n + 2) → ((T.presNext hfW).diag.obj a ⟶ presW.diag.obj a) :=
  Fin.snoc (fun j ↦ pullback.fst (T.bM.natTrans.app a) (fW.natTrans.app a) ≫ T.πSt a j)
    (pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a))

lemma πMNext_π (j : Fin (n + 2)) (a : A) :
    T.πMNext j ≫ presW.π.app a =
      (T.presNext hfW).π.app a ≫ (AffineEtale.toAffineProEt S).map (T.πStNext hfW a j) := by
  induction j using Fin.lastCases with
  | last =>
    rw [πMNext, πStNext, Fin.snoc_last, Fin.snoc_last]
    exact (T.presNext_π_app_snd hfW a).symm
  | cast j =>
    rw [πMNext, πStNext, Fin.snoc_castSucc, Fin.snoc_castSucc, Category.assoc, T.πM_π,
      CategoryTheory.Functor.map_comp, ← Category.assoc, ← presNext_π_app_fst,
      Category.assoc]

lemma πStNext_nat {a a' : A} (u : a ⟶ a') (j : Fin (n + 2)) :
    (T.presNext hfW).diag.map u ≫ T.πStNext hfW a' j =
      T.πStNext hfW a j ≫ presW.diag.map u := by
  induction j using Fin.lastCases with
  | last =>
    rw [πStNext, πStNext, Fin.snoc_last, Fin.snoc_last, presNext_diag_map,
      pullback.lift_snd]
  | cast j =>
    rw [πStNext, πStNext, Fin.snoc_castSucc, Fin.snoc_castSucc, presNext_diag_map,
      pullback.lift_fst_assoc, Category.assoc, T.πSt_nat, Category.assoc]

/-- The étale Čech nerve data of the next level of the tower. -/
noncomputable def étNext (a : A) :
    IsCechNerveAt ((AffineEtale.Spec S).map (fW.natTrans.app a)) (n + 1)
      ((AffineEtale.Spec S).obj ((T.presNext hfW).diag.obj a)) := by
  have sq : IsPullback
      ((AffineEtale.Spec S).map (pullback.fst (T.bM.natTrans.app a) (fW.natTrans.app a)))
      ((AffineEtale.Spec S).map (pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a)))
      ((T.ét a).base) ((AffineEtale.Spec S).map (fW.natTrans.app a)) := by
    rw [T.ét_base a]
    exact (IsPullback.of_hasPullback (T.bM.natTrans.app a) (fW.natTrans.app a)).map
      (AffineEtale.Spec S)
  refine (T.ét a).succ sq (fun j ↦ (AffineEtale.Spec S).map (T.πStNext hfW a j))
    ((AffineEtale.Spec S).map ((T.bMNext hfW).natTrans.app a)) ?_ ?_ ?_
  · intro j
    simp only [πStNext, Fin.snoc_castSucc, CategoryTheory.Functor.map_comp, T.ét_π a j]
  · simp only [πStNext, Fin.snoc_last]
  · rw [bMNext_app, CategoryTheory.Functor.map_comp]

/-- The pro-étale Čech nerve data of the next level of the tower. -/
noncomputable def proNext :
    IsCechNerveAt ((AffineProEt.toProEt S).map q) (n + 1)
      ((AffineProEt.toProEt S).obj (pullback T.bM.map q)) := by
  have sq : IsPullback
      ((AffineProEt.toProEt S).map (pullback.fst T.bM.map q))
      ((AffineProEt.toProEt S).map (pullback.snd T.bM.map q))
      (T.pro.base) ((AffineProEt.toProEt S).map q) := by
    rw [T.pro_base]
    exact (IsPullback.of_hasPullback T.bM.map q).map (AffineProEt.toProEt S)
  refine T.pro.succ sq (fun j ↦ (AffineProEt.toProEt S).map (T.πMNext j))
    ((AffineProEt.toProEt S).map ((T.bMNext hfW).map)) ?_ ?_ ?_
  · intro j
    simp only [πMNext, Fin.snoc_castSucc, CategoryTheory.Functor.map_comp, T.pro_π j]
  · simp only [πMNext, Fin.snoc_last]
  · rw [bMNext_map, CategoryTheory.Functor.map_comp]

/-- The next level of the tower. -/
noncomputable def succ : CechTower q presU presW fW (n + 1) where
  M := pullback T.bM.map q
  presM := T.presNext hfW
  bM := T.bMNext hfW
  πM := T.πMNext
  πSt := T.πStNext hfW
  πM_π := T.πMNext_π hfW
  πSt_nat := T.πStNext_nat hfW
  ét := T.étNext hfW
  ét_π _ _ := rfl
  ét_base _ := rfl
  pro := T.proNext hfW
  pro_π _ := rfl
  pro_base := rfl

end CechTower

namespace CechTower

variable {q presU presW fW} {n : ℕ}
variable (T' : CechTower q presU presW fW (n + 1)) (T : CechTower q presU presW fW n)

lemma ét_π_nat {a a' : A} (u : a ⟶ a') (j : Fin (n + 1)) :
    (AffineEtale.Spec S).map (T.presM.diag.map u) ≫ (T.ét a').π j =
      (T.ét a).π j ≫ (AffineEtale.Spec S).map (presW.diag.map u) := by
  rw [T.ét_π a', T.ét_π a, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, T.πSt_nat u]

lemma ét_base_nat {a a' : A} (u : a ⟶ a') :
    (AffineEtale.Spec S).map (T.presM.diag.map u) ≫ (T.ét a').base =
      (T.ét a).base ≫ (AffineEtale.Spec S).map (presU.diag.map u) := by
  rw [T.ét_base a', T.ét_base a, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, T.bM.natTrans.naturality u]

/-- The stage-wise face maps of consecutive levels of the tower assemble into a morphism
of presentations. -/
noncomputable def faceHom (i : Fin (n + 2)) : T'.presM.Hom T.presM where
  natTrans :=
    { app a := (AffineEtale.Spec S).preimage ((T'.ét a).face (T.ét a) i)
      naturality a a' u := by
        apply (AffineEtale.Spec S).map_injective
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
          Functor.map_preimage, Functor.map_preimage]
        apply (T.ét a').hom_ext
        · intro j
          have hL : ((AffineEtale.Spec S).map (T'.presM.diag.map u) ≫
              (T'.ét a').face (T.ét a') i) ≫ (T.ét a').π j =
                (T'.ét a).π ((SimplexCategory.δ i).toOrderHom j) ≫
                  (AffineEtale.Spec S).map (presW.diag.map u) := by
            rw [Category.assoc, IsCechNerveAt.face_π, T'.ét_π_nat u]
          have hR : ((T'.ét a).face (T.ét a) i ≫
              (AffineEtale.Spec S).map (T.presM.diag.map u)) ≫ (T.ét a').π j =
                (T'.ét a).π ((SimplexCategory.δ i).toOrderHom j) ≫
                  (AffineEtale.Spec S).map (presW.diag.map u) := by
            rw [Category.assoc, T.ét_π_nat u, ← Category.assoc, IsCechNerveAt.face_π]
          rw [hL, hR]
        · have hL : ((AffineEtale.Spec S).map (T'.presM.diag.map u) ≫
              (T'.ét a').face (T.ét a') i) ≫ (T.ét a').base =
                (T'.ét a).base ≫ (AffineEtale.Spec S).map (presU.diag.map u) := by
            rw [Category.assoc, IsCechNerveAt.face_base, T'.ét_base_nat u]
          have hR : ((T'.ét a).face (T.ét a) i ≫
              (AffineEtale.Spec S).map (T.presM.diag.map u)) ≫ (T.ét a').base =
                (T'.ét a).base ≫ (AffineEtale.Spec S).map (presU.diag.map u) := by
            rw [Category.assoc, T.ét_base_nat u, ← Category.assoc, IsCechNerveAt.face_base]
          rw [hL, hR] }

@[simp]
lemma faceHom_app (i : Fin (n + 2)) (a : A) :
    (AffineEtale.Spec S).map ((T'.faceHom T i).natTrans.app a) =
      (T'.ét a).face (T.ét a) i :=
  Functor.map_preimage _ _

lemma faceHom_app_comp_πSt (i : Fin (n + 2)) (a : A) (j : Fin (n + 1)) :
    (T'.faceHom T i).natTrans.app a ≫ T.πSt a j =
      T'.πSt a ((SimplexCategory.δ i).toOrderHom j) := by
  apply (AffineEtale.Spec S).map_injective
  rw [CategoryTheory.Functor.map_comp, faceHom_app, ← T.ét_π, IsCechNerveAt.face_π,
    T'.ét_π]

lemma faceHom_app_comp_bM (i : Fin (n + 2)) (a : A) :
    (T'.faceHom T i).natTrans.app a ≫ T.bM.natTrans.app a = T'.bM.natTrans.app a := by
  apply (AffineEtale.Spec S).map_injective
  rw [CategoryTheory.Functor.map_comp, faceHom_app, ← T.ét_base, IsCechNerveAt.face_base,
    T'.ét_base]

lemma faceHom_map_comp_πM (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (T'.faceHom T i).map ≫ T.πM j = T'.πM ((SimplexCategory.δ i).toOrderHom j) := by
  apply presW.isLimit.hom_ext
  intro a
  rw [Category.assoc, T.πM_π j a, T'.πM_π ((SimplexCategory.δ i).toOrderHom j) a,
    ← Category.assoc, (T'.faceHom T i).map_π a, Category.assoc,
    ← CategoryTheory.Functor.map_comp, faceHom_app_comp_πSt]

lemma faceHom_map_comp_bM (i : Fin (n + 2)) :
    (T'.faceHom T i).map ≫ T.bM.map = T'.bM.map := by
  apply presU.isLimit.hom_ext
  intro a
  rw [Category.assoc, T.bM.map_π a, ← Category.assoc, (T'.faceHom T i).map_π a,
    Category.assoc, ← CategoryTheory.Functor.map_comp, faceHom_app_comp_bM,
    T'.bM.map_π a]

lemma map_faceHom_map (i : Fin (n + 2)) :
    (AffineProEt.toProEt S).map ((T'.faceHom T i).map) = T'.pro.face T.pro i := by
  apply IsCechNerveAt.eq_face
  · intro j
    rw [T.pro_π, T'.pro_π, ← CategoryTheory.Functor.map_comp, faceHom_map_comp_πM]
  · rw [T.pro_base, T'.pro_base, ← CategoryTheory.Functor.map_comp, faceHom_map_comp_bM]


end CechTower

variable {q presU presW fW} in
/-- The tower of iterated fibre products of `q`. -/
noncomputable def cechTower (hfW : fW.map = q) : ∀ n, CechTower q presU presW fW n :=
  fun n ↦ Nat.rec (CechTower.zero hfW) (fun _ T ↦ T.succ hfW) n

end Tower

end AlgebraicGeometry.Scheme.AffineProEt
