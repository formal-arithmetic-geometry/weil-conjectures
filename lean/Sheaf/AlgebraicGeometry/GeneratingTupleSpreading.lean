/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import Sheaf.RingTheory.GeneratingTupleChain
import Mathlib.Geometry.RingedSpace.Basic

/-! # Spreading elementary tuple changes from a stalk -/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem tupleStep_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {c : ℕ} {f g : Fin c → R}
    (h : Module.GeneratingTupleStep (R := R) f g) :
    Module.GeneratingTupleStep (R := S) (φ ∘ f) (φ ∘ g) := by
  classical
  rcases h with ⟨i, a, h⟩ | ⟨i, j, hij, h⟩ | ⟨i, j, a, hij, h⟩
  · left
    refine ⟨i, Units.map φ.toMonoidHom a, fun k ↦ ?_⟩
    simp only [Function.comp_apply, h k, smul_eq_mul, Units.coe_map]
    split_ifs <;> simp only [map_mul]
    rfl
  · right; left
    refine ⟨i, j, hij, fun k ↦ ?_⟩
    simp only [Function.comp_apply, h k]
    split_ifs <;> rfl
  · right; right
    refine ⟨i, j, φ a, hij, fun k ↦ ?_⟩
    simp only [Function.comp_apply, h k, smul_eq_mul]
    split_ifs <;> simp only [map_add, map_mul]

private theorem tupleChain_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {c : ℕ} {f g : Fin c → R}
    (h : Relation.ReflTransGen (Module.GeneratingTupleStep (R := R)) f g) :
    Relation.ReflTransGen (Module.GeneratingTupleStep (R := S)) (φ ∘ f) (φ ∘ g) := by
  induction h with
  | refl => exact .refl
  | tail h hstep ih => exact ih.tail (tupleStep_map φ hstep)

private theorem unit_germ_lift (X : Scheme.{u}) (x : X) (V : X.Opens)
    (hx : x ∈ V) (a : (X.presheaf.stalk x)ˣ) :
    ∃ (U : X.Opens) (_i : U ⟶ V) (hxU : x ∈ U) (b : Γ(X, U)ˣ),
      X.presheaf.germ U x hxU (b : Γ(X, U)) = a := by
  obtain ⟨W, hWV, hxW, b, hb⟩ := X.presheaf.exists_le_germ_eq (a : X.presheaf.stalk x) hx
  have hunit : IsUnit (X.presheaf.germ W x hxW b) := hb ▸ a.isUnit
  obtain ⟨U, _i, hxU, hu⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ W b x hxW hunit
  obtain ⟨b', hb'⟩ := hu
  refine ⟨U, _i ≫ homOfLE hWV, hxU, b', ?_⟩
  rw [hb']
  exact (X.presheaf.germ_res_apply _i x hxU b).trans hb

private theorem tuple_germ_eq (X : Scheme.{u}) (x : X) (V : X.Opens)
    (hx : x ∈ V) {c : ℕ} (f g : Fin c → Γ(X, V))
    (h : ∀ k, X.presheaf.germ V x hx (f k) = X.presheaf.germ V x hx (g k)) :
    ∃ (U : X.Opens) (i : U ⟶ V) (_hxU : x ∈ U),
      (fun k ↦ X.presheaf.map i.op (f k)) = fun k ↦ X.presheaf.map i.op (g k) := by
  classical
  choose W hxW i j hij using fun k ↦ X.presheaf.germ_eq x hx hx (f k) (g k) (h k)
  let U : X.Opens := V ⊓ ⨅ k, W k
  have hxU : x ∈ U := by
    change x ∈ V ∧ x ∈ (⨅ k, W k : X.Opens)
    exact ⟨hx, by simpa only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter] using hxW⟩
  let iUV : U ⟶ V := homOfLE inf_le_left
  refine ⟨U, iUV, hxU, funext fun k ↦ ?_⟩
  let q : U ⟶ W k := homOfLE (inf_le_right.trans (iInf_le W k))
  have hi : q ≫ i k = iUV := Subsingleton.elim _ _
  have hj : q ≫ j k = iUV := Subsingleton.elim _ _
  have he := congrArg (fun t ↦ X.presheaf.map q.op t) (hij k)
  simpa only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, hi, hj] using he

private theorem tuple_step_lift (X : Scheme.{u}) (x : X) (V : X.Opens)
    (hx : x ∈ V) {c : ℕ} (f : Fin c → Γ(X, V)) (g : Fin c → X.presheaf.stalk x)
    (h : Module.GeneratingTupleStep (R := X.presheaf.stalk x)
      (fun k ↦ X.presheaf.germ V x hx (f k)) g) :
    ∃ (U : X.Opens) (i : U ⟶ V) (hxU : x ∈ U) (g' : Fin c → Γ(X, U)),
      Module.GeneratingTupleStep (R := Γ(X, U))
        (fun k ↦ X.presheaf.map i.op (f k)) g' ∧
      ∀ k, X.presheaf.germ U x hxU (g' k) = g k := by
  classical
  rcases h with ⟨j, a, h⟩ | ⟨j, l, hjl, h⟩ | ⟨j, l, a, hjl, h⟩
  · obtain ⟨U, i, hxU, b, hb⟩ := unit_germ_lift X x V hx a
    let f' := fun k ↦ X.presheaf.map i.op (f k)
    let g' := fun k ↦ if k = j then (b : Γ(X, U)) * f' j else f' k
    refine ⟨U, i, hxU, g', Or.inl ⟨j, b, fun k ↦ rfl⟩, fun k ↦ ?_⟩
    rw [h k]
    by_cases hk : k = j
    · simp only [g', f', if_pos hk, smul_eq_mul, map_mul, hb,
        X.presheaf.germ_res_apply]
    · simp only [g', f', if_neg hk, X.presheaf.germ_res_apply]
  · let g' := fun k ↦ if k = j then f l else if k = l then f j else f k
    refine ⟨V, 𝟙 V, hx, g', ?_, fun k ↦ ?_⟩
    · right; left
      refine ⟨j, l, hjl, fun k ↦ ?_⟩
      simp [g']
    · rw [h k]
      by_cases hk : k = j
      · simp only [g', if_pos hk]
      · by_cases hl : k = l
        · simp only [g', if_neg hk, if_pos hl]
        · simp only [g', if_neg hk, if_neg hl]
  · obtain ⟨U, hUV, hxU, b, hb⟩ := X.presheaf.exists_le_germ_eq a hx
    let i : U ⟶ V := homOfLE hUV
    let f' := fun k ↦ X.presheaf.map i.op (f k)
    let g' := fun k ↦ if k = j then f' j + b * f' l else f' k
    refine ⟨U, i, hxU, g', Or.inr (Or.inr ⟨j, l, b, hjl, fun k ↦ rfl⟩), fun k ↦ ?_⟩
    rw [h k]
    by_cases hk : k = j
    · simp only [g', f', if_pos hk, smul_eq_mul, map_add, map_mul, hb,
        X.presheaf.germ_res_apply]
    · simp only [g', f', if_neg hk, X.presheaf.germ_res_apply]

private theorem tuple_chain_lift (X : Scheme.{u}) (x : X) {c : ℕ}
    {a b : Fin c → X.presheaf.stalk x}
    (h : Relation.ReflTransGen (Module.GeneratingTupleStep (R := X.presheaf.stalk x)) a b)
    (V : X.Opens) (hx : x ∈ V) (f : Fin c → Γ(X, V))
    (hf : ∀ k, X.presheaf.germ V x hx (f k) = a k) :
    ∃ (U : X.Opens) (i : U ⟶ V) (hxU : x ∈ U) (g : Fin c → Γ(X, U)),
      Relation.ReflTransGen (Module.GeneratingTupleStep (R := Γ(X, U)))
        (fun k ↦ X.presheaf.map i.op (f k)) g ∧
      ∀ k, X.presheaf.germ U x hxU (g k) = b k := by
  classical
  induction h generalizing V f with
  | refl =>
    refine ⟨V, 𝟙 V, hx, f, ?_, hf⟩
    have hid : (𝟙 V : V ⟶ V).op = 𝟙 (op V) := rfl
    simp only [hid]
    rw [X.presheaf.map_id]
    exact .refl
  | @tail b d hab hbd ih =>
    obtain ⟨U, i, hxU, g, hfg, hg⟩ := ih V hx f hf
    have hbd' : Module.GeneratingTupleStep (R := X.presheaf.stalk x)
        (fun k ↦ X.presheaf.germ U x hxU (g k)) d := by
      convert hbd using 1
      exact funext hg
    obtain ⟨W, j, hxW, g', hgg', hg'⟩ := tuple_step_lift X x U hxU g d hbd'
    refine ⟨W, j ≫ i, hxW, g', ?_, hg'⟩
    have hm := tupleChain_map (X.presheaf.map j.op).hom hfg
    have hc := hm.tail hgg'
    change Relation.ReflTransGen _
      (fun k ↦ X.presheaf.map j.op (X.presheaf.map i.op (f k))) g' at hc
    simpa only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply] using hc

/-- Equal spans of two tuples become an actual finite chain of elementary changes
on a neighbourhood of every point. No Noetherian hypothesis is needed.
Source: the local-ring and spreading paragraph of frame independence
(blueprint: lem-pur-generating-tuple-spreading).
Proof: map the common span to the stalk. The local ring generator theorem gives
an elementary chain there. Lift each coefficient to a neighbourhood; for a unit,
lift it and shrink until it is invertible. Induct through the finite chain,
restricting its earlier steps at each shrinking. Finally, equality of the finitely
many endpoint germs spreads to equality of the endpoint sections. -/
theorem generatingTupleChain_neighbourhood (X : Scheme.{u}) (x : X) (V : X.Opens)
    (hx : x ∈ V) (c : ℕ) (f g : Fin c → Γ(X, V))
    (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    ∃ (U : X.Opens) (i : U ⟶ V) (_hxU : x ∈ U),
      Relation.ReflTransGen (Module.GeneratingTupleStep (R := Γ(X, U)))
        (fun k ↦ X.presheaf.map i.op (f k)) (fun k ↦ X.presheaf.map i.op (g k)) := by
  let φ := (X.presheaf.germ V x hx).hom
  have hs : Ideal.span (Set.range (φ ∘ f)) = Ideal.span (Set.range (φ ∘ g)) := by
    simpa only [Ideal.map_span, ← Set.range_comp] using congrArg (Ideal.map φ) hfg
  have hc := Module.generatingTupleChain c (φ ∘ f) (φ ∘ g) hs
  obtain ⟨W, i, hxW, h, hfh, hh⟩ := tuple_chain_lift X x hc V hx f (fun _ ↦ rfl)
  have hgerm (k : Fin c) : X.presheaf.germ W x hxW (h k) =
      X.presheaf.germ W x hxW (X.presheaf.map i.op (g k)) := by
    rw [X.presheaf.germ_res_apply]
    exact hh k
  obtain ⟨U, j, hxU, heq⟩ := tuple_germ_eq X x W hxW h
    (fun k ↦ X.presheaf.map i.op (g k)) hgerm
  refine ⟨U, j ≫ i, hxU, ?_⟩
  have hc' := tupleChain_map (X.presheaf.map j.op).hom hfh
  rw [show (X.presheaf.map j.op).hom ∘ h =
    (fun k ↦ X.presheaf.map j.op (X.presheaf.map i.op (g k))) from heq] at hc'
  change Relation.ReflTransGen _
    (fun k ↦ X.presheaf.map j.op (X.presheaf.map i.op (f k)))
    (fun k ↦ X.presheaf.map j.op (X.presheaf.map i.op (g k))) at hc'
  simpa only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply] using hc'

/-- Tuples defining the same ideal sheaf are connected by elementary changes locally.
The conclusion retains actual scheme global sections on each open subscheme.
Source: the affine-neighbourhood reduction in frame independence
(blueprint: lem-pur-generating-tuple-spreading).
Proof: choose an affine neighbourhood of the point. Evaluation of the ideal-sheaf
identity gives equal spans of the restricted functions. Apply the neighbourhood
chain theorem and transport through the restriction/global-section ring isomorphism. -/
theorem generatingTupleChain_of_idealSheaf_eq (X : Scheme.{u}) (c : ℕ)
    (f g : Fin c → Γ(X, ⊤))
    (hfg : Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range f)) =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range g)) : X.IdealSheafData))
    (x : X) :
    ∃ (U : X.Opens) (_hxU : x ∈ U),
      Relation.ReflTransGen (Module.GeneratingTupleStep (R := Γ(U.toScheme, ⊤)))
        (fun k ↦ U.ι.appTop (f k)) (fun k ↦ U.ι.appTop (g k)) := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := x) (by trivial)
  have hv := congrArg (fun I : X.IdealSheafData ↦ I.ideal ⟨V, hV⟩) hfg
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span,
    ← Set.range_comp] at hv
  obtain ⟨U, i, hxU, hc⟩ := generatingTupleChain_neighbourhood X x V hxV c
    (fun k ↦ X.presheaf.map (homOfLE le_top).op (f k))
    (fun k ↦ X.presheaf.map (homOfLE le_top).op (g k)) hv
  have hh := tupleChain_map U.topIso.inv.hom hc
  refine ⟨U, hxU, ?_⟩
  have hres (t : Γ(X, ⊤)) : U.topIso.inv
      (X.presheaf.map i.op (X.presheaf.map (homOfLE le_top).op t)) = U.ι.appTop t := by
    simp only [Scheme.Opens.topIso, Scheme.Opens.ι_appTop, Functor.mapIso_inv,
      ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl
  change Relation.ReflTransGen _
    (fun k ↦ U.topIso.inv (X.presheaf.map i.op
      (X.presheaf.map (homOfLE le_top).op (f k))))
    (fun k ↦ U.topIso.inv (X.presheaf.map i.op
      (X.presheaf.map (homOfLE le_top).op (g k)))) at hh
  simpa only [hres] using hh

end AlgebraicGeometry
