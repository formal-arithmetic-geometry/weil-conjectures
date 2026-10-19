/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.FrameElementaryMoves
import Sheaf.RingTheory.LocalGeneratingTuples
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-! # Local elementary chains between two presentations of a closed subscheme

Source: main-20261015, lem-pur-frame-independence.proof.md, local-ring reduction.
(blueprint: lem-pur-frame-local-generator-chains).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting

private theorem elementary_move_map {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {c : ℕ} {f g : Fin c → R} (h : FrameElementaryMove f g) :
    FrameElementaryMove (φ ∘ f) (φ ∘ g) := by
  classical
  rcases h with ⟨i, a, h⟩ | ⟨i, j, hij, h⟩ | ⟨i, j, a, hij, h⟩
  · left
    refine ⟨i, Units.map φ.toMonoidHom a, ?_⟩
    intro k
    dsimp only [Function.comp_apply]
    rw [h k]
    split_ifs <;> simp
  · right; left
    refine ⟨i, j, hij, ?_⟩
    intro k
    dsimp only [Function.comp_apply]
    rw [h k]
    split_ifs <;> rfl
  · right; right
    refine ⟨i, j, φ a, hij, ?_⟩
    intro k
    dsimp only [Function.comp_apply]
    rw [h k]
    split_ifs <;> simp

private theorem elementary_chain_map {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {c : ℕ} {f g : Fin c → R}
    (h : Relation.ReflTransGen FrameElementaryMove f g) :
    Relation.ReflTransGen FrameElementaryMove (φ ∘ f) (φ ∘ g) := by
  induction h with
  | refl => exact .refl
  | tail h hstep ih => exact ih.tail (elementary_move_map φ hstep)

private theorem elementary_chain_of_span_eq {R : Type u} [CommRing R] [IsLocalRing R]
    {c : ℕ} (f g : Fin c → R) (hspan : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    Relation.ReflTransGen FrameElementaryMove f g := by
  classical
  let I := Ideal.span (Set.range f)
  let f' : Fin c → I := fun k ↦ ⟨f k, Ideal.subset_span ⟨k, rfl⟩⟩
  let g' : Fin c → I := fun k ↦ ⟨g k, hspan.ge (Ideal.subset_span ⟨k, rfl⟩)⟩
  have hfg : I.FG := Submodule.fg_def.mpr ⟨Set.range f, Set.finite_range f, rfl⟩
  let : Module.Finite R I := Module.Finite.of_fg hfg
  have hf' : Submodule.span R (Set.range f') = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff I (fun k ↦ (f' k).property)).mpr rfl
  have hg' : Submodule.span R (Set.range g') = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff I (fun k ↦ (g' k).property)).mpr hspan.symm
  obtain ⟨n, x, A, hzero, hend, hsteps, _⟩ :=
    Module.exists_elementary_generating_tuple_change c f' g' hf' hg'
  have hchain : ∀ t, t ≤ n →
      Relation.ReflTransGen FrameElementaryMove f (fun k ↦ (x t k : R)) := by
    intro t ht
    induction t with
    | zero => simpa only [hzero] using (Relation.ReflTransGen.refl (a := f))
    | succ t ih =>
      refine (ih (Nat.le_of_succ_le ht)).tail ?_
      rcases hsteps t (Nat.lt_of_succ_le ht) with
        ⟨i, a, h, _⟩ | ⟨i, j, hij, h, _⟩ | ⟨i, j, a, hij, h, _⟩
      · left
        refine ⟨i, a, ?_⟩
        intro k
        simpa only [apply_ite, Submodule.coe_smul_of_tower, smul_eq_mul] using
          congrArg (fun z : I ↦ (z : R)) (h k)
      · right; left
        refine ⟨i, j, hij, ?_⟩
        intro k
        have hk := congrArg (fun z : I ↦ (z : R)) (h k)
        split_ifs at hk ⊢ <;> exact hk
      · right; right
        refine ⟨i, j, a, hij, ?_⟩
        intro k
        simpa only [apply_ite, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul] using
          congrArg (fun z : I ↦ (z : R)) (h k)
  simpa only [hend] using hchain n le_rfl

private theorem finite_germ_lift (X : Scheme.{u}) (x : X) (V : X.Opens) (hxV : x ∈ V)
    {ι : Type*} [Finite ι] (t : ι → X.presheaf.stalk x) :
    ∃ (W : X.Opens) (_hWV : W ≤ V) (hxW : x ∈ W) (s : ι → Γ(X, W)),
      ∀ i, X.presheaf.germ W x hxW (s i) = t i := by
  classical
  let := Fintype.ofFinite ι
  have h (S : Finset ι) :
      ∃ (W : X.Opens) (_hWV : W ≤ V) (hxW : x ∈ W) (s : ι → Γ(X, W)),
        ∀ i ∈ S, X.presheaf.germ W x hxW (s i) = t i := by
    induction S using Finset.induction_on with
    | empty => exact ⟨V, le_rfl, hxV, fun _ ↦ 0, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨W, hWV, hxW, s, hs⟩ := ih
      obtain ⟨T, hTW, hxT, a, ha⟩ := X.presheaf.exists_le_germ_eq (t i) hxW
      refine ⟨T, hTW.trans hWV, hxT,
        fun j ↦ if j = i then a else X.presheaf.map (homOfLE hTW).op (s j), ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa only [ite_true] using ha
      · simp only [hji, ite_false, X.presheaf.germ_res_apply]
        exact hs j ((Finset.mem_insert.mp hj).resolve_left hji)
  obtain ⟨W, hWV, hxW, s, hs⟩ := h Finset.univ
  exact ⟨W, hWV, hxW, s, fun i ↦ hs i (Finset.mem_univ i)⟩

private theorem restrict_eq {X : Scheme.{u}} {V W T : X.Opens} (hWV : W ≤ V)
    (hTW : T ≤ W) {s t : Γ(X, V)}
    (h : X.presheaf.map (homOfLE hWV).op s = X.presheaf.map (homOfLE hWV).op t) :
    X.presheaf.map (homOfLE (hTW.trans hWV)).op s =
      X.presheaf.map (homOfLE (hTW.trans hWV)).op t := by
  simpa only [X.presheaf_map_map] using
    congrArg (fun z ↦ X.presheaf.map (homOfLE hTW).op z) h

private theorem finite_germ_eq (X : Scheme.{u}) (x : X) (V : X.Opens) (hxV : x ∈ V)
    {ι : Type*} [Finite ι] (s t : ι → Γ(X, V))
    (h : ∀ i, X.presheaf.germ V x hxV (s i) = X.presheaf.germ V x hxV (t i)) :
    ∃ (W : X.Opens) (hWV : W ≤ V), x ∈ W ∧
      ∀ i, X.presheaf.map (homOfLE hWV).op (s i) =
        X.presheaf.map (homOfLE hWV).op (t i) := by
  classical
  let := Fintype.ofFinite ι
  have hS (S : Finset ι) : ∃ (W : X.Opens) (hWV : W ≤ V), x ∈ W ∧
      ∀ i ∈ S, X.presheaf.map (homOfLE hWV).op (s i) =
        X.presheaf.map (homOfLE hWV).op (t i) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨V, le_rfl, hxV, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨W, hWV, hxW, hW⟩ := ih
      obtain ⟨T, hxT, j, k, hT⟩ := X.presheaf.germ_eq x hxV hxV (s i) (t i) (h i)
      have hTV : T ≤ V := leOfHom j
      have hT' : X.presheaf.map (homOfLE hTV).op (s i) =
          X.presheaf.map (homOfLE hTV).op (t i) := hT
      refine ⟨W ⊓ T, inf_le_left.trans hWV, ⟨hxW, hxT⟩, ?_⟩
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact restrict_eq hTV inf_le_right hT'
      · exact restrict_eq hWV inf_le_left (hW l hl)
  obtain ⟨W, hWV, hxW, hW⟩ := hS Finset.univ
  exact ⟨W, hWV, hxW, fun i ↦ hW i (Finset.mem_univ i)⟩

private def GermFrameChain (X : Scheme.{u}) (x : X) (c : ℕ)
    (f g : Fin c → X.presheaf.stalk x) : Prop :=
  ∃ (W : X.Opens) (hxW : x ∈ W) (s t : Fin c → Γ(X, W)),
    (∀ k, X.presheaf.germ W x hxW (s k) = f k) ∧
    (∀ k, X.presheaf.germ W x hxW (t k) = g k) ∧
    Relation.ReflTransGen FrameElementaryMove s t

private theorem germ_chain_refl (X : Scheme.{u}) (x : X) (c : ℕ)
    (f : Fin c → X.presheaf.stalk x) : GermFrameChain X x c f f := by
  obtain ⟨W, _, hxW, s, hs⟩ := finite_germ_lift X x ⊤ trivial f
  exact ⟨W, hxW, s, s, hs, hs, .refl⟩

private theorem germ_chain_single (X : Scheme.{u}) (x : X) (c : ℕ)
    (f g : Fin c → X.presheaf.stalk x) (h : FrameElementaryMove f g) :
    GermFrameChain X x c f g := by
  classical
  obtain ⟨W, _, hxW, s, hs⟩ := finite_germ_lift X x ⊤ trivial f
  rcases h with ⟨i, a, h⟩ | ⟨i, j, hij, h⟩ | ⟨i, j, a, hij, h⟩
  · obtain ⟨T, hTW, hxT, b, hb⟩ :=
      X.presheaf.exists_le_germ_eq (a : X.presheaf.stalk x) hxW
    obtain ⟨N, k, hxN, hbN⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ T b x hxT
      (hb.symm ▸ a.isUnit)
    obtain ⟨b', hb'⟩ := hbN
    let ρ := (X.presheaf.map (k ≫ homOfLE hTW).op).hom
    let t : Fin c → Γ(X, N) := fun l ↦
      if l = i then (b' : Γ(X, N)) * ρ (s i) else ρ (s l)
    have hsN : ∀ l, X.presheaf.germ N x hxN (ρ (s l)) = f l := by
      intro l
      simpa only [ρ, CommRingCat.hom_comp, TopCat.Presheaf.germ_res_apply] using hs l
    refine ⟨N, hxN, ρ ∘ s, t, hsN, ?_, .single (Or.inl ⟨i, b', ?_⟩)⟩
    · intro l
      dsimp only [t]
      rw [h l]
      split_ifs
      · rw [map_mul, hsN]
        congr 1
        rw [hb', X.presheaf.germ_res_apply, hb]
      · exact hsN l
    · intro l
      rfl
  · let t : Fin c → Γ(X, W) := fun l ↦
      if l = i then s j else if l = j then s i else s l
    refine ⟨W, hxW, s, t, hs, ?_, .single (Or.inr (Or.inl ⟨i, j, hij, ?_⟩))⟩
    · intro l
      dsimp only [t]
      rw [h l]
      split_ifs <;> apply hs
    · intro l
      rfl
  · obtain ⟨T, hTW, hxT, b, hb⟩ := X.presheaf.exists_le_germ_eq a hxW
    let ρ := (X.presheaf.map (homOfLE hTW).op).hom
    let t : Fin c → Γ(X, T) := fun l ↦
      if l = i then ρ (s i) + b * ρ (s j) else ρ (s l)
    have hsT : ∀ l, X.presheaf.germ T x hxT (ρ (s l)) = f l := by
      intro l
      simpa only [ρ, TopCat.Presheaf.germ_res_apply] using hs l
    refine ⟨T, hxT, ρ ∘ s, t, hsT, ?_, .single (Or.inr (Or.inr ⟨i, j, b, hij, ?_⟩))⟩
    · intro l
      dsimp only [t]
      rw [h l]
      split_ifs
      · rw [map_add, map_mul, hsT, hsT, hb]
      · exact hsT l
    · intro l
      rfl

private theorem germ_chain_trans (X : Scheme.{u}) (x : X) (c : ℕ)
    {f g h : Fin c → X.presheaf.stalk x}
    (hfg : GermFrameChain X x c f g) (hgh : GermFrameChain X x c g h) :
    GermFrameChain X x c f h := by
  obtain ⟨W, hxW, s, t, hs, ht, hst⟩ := hfg
  obtain ⟨T, hxT, t', v, ht', hv, htv⟩ := hgh
  let ρ := (X.presheaf.map (homOfLE (inf_le_left : W ⊓ T ≤ W)).op).hom
  let σ := (X.presheaf.map (homOfLE (inf_le_right : W ⊓ T ≤ T)).op).hom
  have heq : ∀ k,
      X.presheaf.germ (W ⊓ T) x ⟨hxW, hxT⟩ (ρ (t k)) =
        X.presheaf.germ (W ⊓ T) x ⟨hxW, hxT⟩ (σ (t' k)) := by
    intro k
    simpa only [ρ, σ, TopCat.Presheaf.germ_res_apply] using (ht k).trans (ht' k).symm
  obtain ⟨N, hN, hxN, heqN⟩ := finite_germ_eq X x (W ⊓ T) ⟨hxW, hxT⟩
    (ρ ∘ t) (σ ∘ t') heq
  let τ := (X.presheaf.map (homOfLE hN).op).hom
  have hmid : τ ∘ (ρ ∘ t) = τ ∘ (σ ∘ t') := funext heqN
  refine ⟨N, hxN, τ ∘ (ρ ∘ s), τ ∘ (σ ∘ v), ?_, ?_, ?_⟩
  · intro k
    simpa only [Function.comp_apply, τ, ρ, TopCat.Presheaf.germ_res_apply] using hs k
  · intro k
    simpa only [Function.comp_apply, τ, σ, TopCat.Presheaf.germ_res_apply] using hv k
  · exact (elementary_chain_map τ (elementary_chain_map ρ hst)).trans
      (hmid.symm ▸ elementary_chain_map τ (elementary_chain_map σ htv))

private theorem appTop_eq_restrict (X : Scheme.{u}) (W : X.Opens) (a : Γ(X, ⊤)) :
    W.ι.appTop a = W.topIso.inv (X.presheaf.map (homOfLE le_top).op a) := by
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop]
  change _ = (X.presheaf.map _ ≫ X.presheaf.map _) a
  rw [← Functor.map_comp]
  rfl

/-- Two equal-length presentations of a fixed scheme-theoretic inverse image are connected
by elementary generator moves on an affine neighbourhood of each point.

Source: main-20261015, lem-pur-frame-independence.proof.md, local-ring reduction,
with `Module.exists_elementary_generating_tuple_change` and germ shrinking
(blueprint: lem-pur-frame-local-generator-chains).

Proof: Restrict to an affine neighbourhood of the chosen point. The two pullback
squares identify the ideals generated by the restricted tuples, by
`Scheme.span_eq_of_isPullback_zeroLocusSubschemeι`; this uses etaleness of the
map. Pass to the local ring at the point. The two tuples generate the same
finite ideal module, so `Module.exists_elementary_generating_tuple_change` gives
a finite chain of unit scalings, permutations and shears. For every coefficient,
unit inverse and equation in the finite chain, use `Presheaf.exists_germ_eq` and
`Presheaf.germ_eq` to choose a common smaller open on which the equality holds.
Intersect the finitely many opens and choose an affine subopen. Restrictions
preserve each elementary operation and its endpoint equations. For `c = 0` the
empty tuple gives the reflexive chain. The construction is local and remains
valid for empty supports.

The statement is strictly below frame independence: it only produces the local
finite chain of changes of generators and mentions no cohomology class. -/
theorem exists_frame_local_generator_chain {V Z U : Scheme.{u}}
    (i : Z ⟶ V) [IsClosedImmersion i] (e : U ⟶ V) [Etale e] (c : ℕ)
    (f g : Fin c → Γ(U, ⊤))
    (tf : U.zeroLocusSubscheme (Set.range f) ⟶ Z)
    (tg : U.zeroLocusSubscheme (Set.range g) ⟶ Z)
    (hf : IsPullback tf (U.zeroLocusSubschemeι (Set.range f)) i e)
    (hg : IsPullback tg (U.zeroLocusSubschemeι (Set.range g)) i e)
    (x : U) :
    ∃ W : U.Opens, x ∈ W ∧ IsAffineOpen W ∧
      Relation.ReflTransGen FrameElementaryMove
        (fun k ↦ W.ι.appTop (f k)) (fun k ↦ W.ι.appTop (g k)) := by
  classical
  obtain ⟨N, hN, hxN, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : U.Opens) from trivial)
  let : IsAffine N.toScheme := hN
  let fN : Fin c → Γ(N.toScheme, ⊤) := fun k ↦ N.ι.appTop (f k)
  let gN : Fin c → Γ(N.toScheme, ⊤) := fun k ↦ N.ι.appTop (g k)
  have hfp := Scheme.isPullback_zeroLocusSubschemeι N.ι (Set.range f) (Set.range fN)
    (by rw [← Set.range_comp]; rfl)
  have hgp := Scheme.isPullback_zeroLocusSubschemeι N.ι (Set.range g) (Set.range gN)
    (by rw [← Set.range_comp]; rfl)
  have hspan : Ideal.span (Set.range fN) = Ideal.span (Set.range gN) :=
    Scheme.span_eq_of_isPullback_zeroLocusSubschemeι (hfp.paste_horiz hf) (hgp.paste_horiz hg)
  let ρ : Γ(N.toScheme, ⊤) →+* U.presheaf.stalk x :=
    (U.presheaf.germ N x hxN).hom.comp N.topIso.hom.hom
  have hρ (a : Γ(U, ⊤)) : ρ (N.ι.appTop a) = U.presheaf.germ ⊤ x trivial a := by
    rw [appTop_eq_restrict]
    dsimp only [ρ, RingHom.comp_apply]
    rw [Iso.inv_hom_id_apply, U.presheaf.germ_res_apply]
  have hspan' : Ideal.span (Set.range (fun k ↦ U.presheaf.germ ⊤ x trivial (f k))) =
      Ideal.span (Set.range (fun k ↦ U.presheaf.germ ⊤ x trivial (g k))) := by
    have hh := congrArg (Ideal.map ρ) hspan
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, fN, gN, hρ] using hh
  have hc := elementary_chain_of_span_eq _ _ hspan'
  have hall : ∀ {a b : Fin c → U.presheaf.stalk x},
      Relation.ReflTransGen FrameElementaryMove a b → GermFrameChain U x c a b := by
    intro a b h
    induction h using Relation.ReflTransGen.trans_induction_on with
    | refl => exact germ_chain_refl U x c _
    | single h => exact germ_chain_single U x c _ _ h
    | trans _ _ ih₁ ih₂ => exact germ_chain_trans U x c ih₁ ih₂
  obtain ⟨W, hxW, s, t, hs, ht, hst⟩ := hall hc
  let fW : Fin c → Γ(U, W) := fun k ↦ U.presheaf.map (homOfLE le_top).op (f k)
  let gW : Fin c → Γ(U, W) := fun k ↦ U.presheaf.map (homOfLE le_top).op (g k)
  obtain ⟨T, hTW, hxT, hTf⟩ := finite_germ_eq U x W hxW s fW (fun k ↦ by
    simpa only [fW, TopCat.Presheaf.germ_res_apply] using hs k)
  let τ := (U.presheaf.map (homOfLE hTW).op).hom
  obtain ⟨Q, hQT, hxQ, hQg⟩ := finite_germ_eq U x T hxT (τ ∘ t) (τ ∘ gW) (fun k ↦ by
    simpa only [τ, Function.comp_apply, gW, TopCat.Presheaf.germ_res_apply] using ht k)
  obtain ⟨D, hD, hxD, hDQ⟩ := exists_isAffineOpen_mem_and_subset hxQ
  have hDQ' : D ≤ Q := hDQ
  let σ := (U.presheaf.map (homOfLE (hDQ'.trans hQT)).op).hom
  let ω : Γ(U, D) →+* Γ(D.toScheme, ⊤) := D.topIso.inv.hom
  have hc'' := elementary_chain_map ω (elementary_chain_map σ (elementary_chain_map τ hst))
  have hleft : ω ∘ (σ ∘ (τ ∘ s)) = fun k ↦ D.ι.appTop (f k) := by
    funext k
    change D.topIso.inv (U.presheaf.map (homOfLE (hDQ'.trans hQT)).op
      (U.presheaf.map (homOfLE hTW).op (s k))) = _
    rw [hTf k]
    dsimp only [fW]
    simp only [U.presheaf_map_map]
    exact (appTop_eq_restrict U D (f k)).symm
  have hright : ω ∘ (σ ∘ (τ ∘ t)) = fun k ↦ D.ι.appTop (g k) := by
    funext k
    have hh := congrArg (fun z ↦ U.presheaf.map (homOfLE hDQ').op z) (hQg k)
    change U.presheaf.map (homOfLE hDQ').op
        (U.presheaf.map (homOfLE hQT).op (U.presheaf.map (homOfLE hTW).op (t k))) =
      U.presheaf.map (homOfLE hDQ').op
        (U.presheaf.map (homOfLE hQT).op (U.presheaf.map (homOfLE hTW).op (gW k))) at hh
    simp only [U.presheaf_map_map] at hh
    change D.topIso.inv (U.presheaf.map (homOfLE (hDQ'.trans hQT)).op
      (U.presheaf.map (homOfLE hTW).op (t k))) = _
    rw [U.presheaf_map_map, hh]
    dsimp only [gW]
    simp only [U.presheaf_map_map]
    exact (appTop_eq_restrict U D (g k)).symm
  rw [hleft, hright] at hc''
  exact ⟨D, hxD, hD, hc''⟩

end WeilConjectures.PurityFiniteSetting
