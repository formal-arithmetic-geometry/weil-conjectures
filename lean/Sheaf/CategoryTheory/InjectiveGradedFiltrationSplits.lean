/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.CategoryTheory.Filtration
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Compatible splitting of a filtration with injective graded pieces

Source: Stacks Project, Derived Categories, Tag 05TP, `lemma-filtered-injective`
(blueprint: lem-trf-injective-graded-filtration-splits).

The interval is fixed in advance. A single isomorphism carries every filtration subobject
onto the corresponding tail of the finite biproduct. The explicit `HasBiproduct` arguments
are the standard finite-product construction, available in every abelian category.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FilteredObject

-- Extend each graded quotient map to the whole object. The resulting map to the
-- biproduct restricts to every tail, and the short five lemma proves those restrictions
-- invertible by descending induction. This avoids choosing compatible splittings.
private abbrev Tail (a b p : ℤ) := {n : Set.Icc a b // p ≤ n.1}

section Tail

variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]
  {a b : ℤ} (J : Set.Icc a b → C)

private abbrev tailFamily (p : ℤ) : Tail a b p → C := fun n ↦ J n.1

private noncomputable def tailInclusion (p : ℤ) :
    ⨁ (tailFamily J (p + 1)) ⟶ ⨁ (tailFamily J p) :=
  biproduct.desc fun n ↦ biproduct.ι (tailFamily J p) ⟨n.1, by have := n.2; omega⟩

private noncomputable def tailRetraction (p : ℤ) :
    ⨁ (tailFamily J p) ⟶ ⨁ (tailFamily J (p + 1)) :=
  biproduct.lift fun n ↦ biproduct.π (tailFamily J p) ⟨n.1, by have := n.2; omega⟩

private noncomputable abbrev tailComplex (p : ℤ) (hp : a ≤ p ∧ p ≤ b) :
    ShortComplex C :=
    ShortComplex.mk (tailInclusion J p)
      (biproduct.π (tailFamily J p) ⟨⟨p, hp⟩, le_rfl⟩) (by
        apply biproduct.hom_ext'
        intro n
        simp only [tailInclusion, biproduct.ι_desc_assoc, comp_zero]
        apply biproduct.ι_π_ne
        intro h
        have hval := congrArg (fun n : Tail a b p ↦ n.1.1) h
        change n.1.1 = p at hval
        have := n.2
        omega)

private theorem tail_shortExact (p : ℤ) (hp : a ≤ p ∧ p ≤ b) :
    (tailComplex J p hp).ShortExact := by
  classical
  dsimp only [tailComplex]
  let j : Tail a b p := ⟨⟨p, hp⟩, le_rfl⟩
  apply ShortComplex.Splitting.shortExact
  refine { r := tailRetraction J p
           s := biproduct.ι (tailFamily J p) j
           f_r := ?_
           s_g := ?_
           id := ?_ }
  · apply biproduct.hom_ext'
    intro n
    apply biproduct.hom_ext
    intro m
    simp only [tailInclusion, tailRetraction, Category.assoc,
      biproduct.ι_desc_assoc, biproduct.lift_π, Category.id_comp]
    simp only [biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ (Subtype.ext (congrArg (fun x : Tail a b p ↦ x.1) h₁)))
    · exact False.elim (h₁ (Subtype.ext (congrArg (fun x : Tail a b (p + 1) ↦ x.1) h₂)))
    · rfl
  · simp [j]
  · apply biproduct.hom_ext'
    intro n
    change biproduct.ι (tailFamily J p) n ≫
      (tailRetraction J p ≫ tailInclusion J p +
        biproduct.π (tailFamily J p) j ≫ biproduct.ι (tailFamily J p) j) =
      biproduct.ι (tailFamily J p) n ≫ 𝟙 _
    by_cases hn : n.1.1 = p
    · have hnj : n = j := Subtype.ext (Subtype.ext hn)
      subst n
      have hz : biproduct.ι (tailFamily J p) j ≫ tailRetraction J p = 0 := by
        apply biproduct.hom_ext
        intro m
        simp only [tailRetraction, Category.assoc, biproduct.lift_π, zero_comp]
        apply biproduct.ι_π_ne
        intro h
        have hval := congrArg (fun n : Tail a b p ↦ n.1.1) h
        change p = m.1.1 at hval
        have := m.2
        omega
      simp [Preadditive.comp_add, ← Category.assoc, hz]
    · let m : Tail a b (p + 1) := ⟨n.1, by have := n.2; omega⟩
      have hr : biproduct.ι (tailFamily J p) n ≫ tailRetraction J p =
          biproduct.ι (tailFamily J (p + 1)) m := by
        apply biproduct.hom_ext
        intro k
        simp only [tailRetraction, Category.assoc, biproduct.lift_π, biproduct.ι_π]
        split_ifs with h₁ h₂ h₂
        · rfl
        · exact False.elim (h₂ (Subtype.ext (congrArg (fun x : Tail a b p ↦ x.1) h₁)))
        · exact False.elim (h₁ (Subtype.ext (congrArg (fun x : Tail a b (p + 1) ↦ x.1) h₂)))
        · rfl
      have hnj : n ≠ j := fun h ↦ hn (congrArg (fun n : Tail a b p ↦ n.1.1) h)
      simp [Preadditive.comp_add, ← Category.assoc, hr, tailInclusion,
        biproduct.ι_π_ne _ hnj, m]

end Tail

/-- A finite filtration with injective graded pieces admits a simultaneous splitting.
Source: Stacks Project, Derived Categories, Tag 05TP, `lemma-filtered-injective`
(blueprint: lem-trf-injective-graded-filtration-splits).

The right-hand subobject is the image of `biproduct.fromSubtype`, the canonical split
inclusion of the summands indexed by `n ≥ p`. Thus the equality specifies the embedded
subobject, not merely an abstract isomorphism of its underlying object.

Proof:
1. Set `J_n = gr^n I` for `a ≤ n ≤ b`. These are injective by hypothesis, with identity
   graded-piece isomorphisms. Put `B_n = ⨁_{n ≤ k ≤ b} J_k`. Descend from `b + 1` to `a`,
   constructing `θ_n : F^n I ≅ B_n` compatible with all inclusions `F^p I → F^n I` for
   `n ≤ p ≤ b + 1`. At `b + 1`, both objects are zero, so compatibility is automatic.
2. By `lem-weil-pbc-product-injectives`, the finite biproduct `B_(n+1)`, including the
   empty one, is injective. Transfer its extension property along `θ_(n+1)` to show
   `F^(n+1) I` is injective.
3. The inclusion `i_n : F^(n+1) I → F^n I` and quotient `q_n : F^n I → J_n` form a short
   exact sequence. By `lem-weil-pbc-ses-injective-kernel-splits`, choose `r_n` and `s_n`
   with `r_n i_n = 1`, `q_n s_n = 1`, and `i_n r_n + s_n q_n = 1` (composition here is
   written in the usual mathematical order).
4. The splitting identities and monicity of `i_n` give `r_n s_n = 0`. Hence `(q_n,r_n)`
   and `(s_n,i_n)` are inverse maps between `F^n I` and `J_n ⊕ F^(n+1) I`: their four
   matrix blocks are `1,0,0,1`. Compose with `1 ⊕ θ_(n+1)` to obtain `θ_n : F^n I ≅ B_n`.
5. Since `q_n i_n = 0` and `r_n i_n = 1`, `θ_n` carries the next inclusion to the tail
   inclusion. Factor every deeper inclusion through this one and use the induction
   hypothesis to get simultaneous compatibility. These equations identify subobjects
   because the maps `θ_p` are isomorphisms.
6. At `a`, use `F^a I = I` to obtain `θ`. Compatibility handles `a ≤ p ≤ b + 1`. If
   `p < a`, decreasingness forces `F^p I = I`, and the tail is the whole biproduct. If
   `p > b + 1`, decreasingness forces `F^p I = 0`, and the tail is empty. Thus the same
   `θ` identifies the required subobjects for every integer `p`. -/
theorem injective_graded_filtration_splits {C : Type u} [Category.{v} C] [Abelian C]
    (X : FilteredObject C) (a b : ℤ) (hab : a ≤ b)
    (ha : X.filtration.F a = ⊤) (hb : X.filtration.F (b + 1) = ⊥)
    (hgr : ∀ n : Set.Icc a b, Injective (X.filtration.gradedPiece n.1)) :
    ∃ J : Set.Icc a b → C,
      (∀ n : Set.Icc a b, Injective (J n)) ∧
      (∀ n : Set.Icc a b, Nonempty (J n ≅ X.filtration.gradedPiece n.1)) ∧
      ∃ θ : X.obj ≅ @biproduct _ C _ _ J (HasBiproduct.of_hasProduct J),
        ∀ p : ℤ, (Subobject.map θ.hom).obj (X.filtration.F p) =
          imageSubobject (@biproduct.fromSubtype _ C _ _ J (HasBiproduct.of_hasProduct J)
            (fun n : Set.Icc a b ↦ p ≤ n.1) (HasBiproduct.of_hasProduct _)) := by
  classical
  let : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  let J : Set.Icc a b → C := fun n ↦ X.filtration.gradedPiece n.1
  let (n : Set.Icc a b) : Injective (J n) := hgr n
  let q (n : ℤ) : (X.filtration.F n : C) ⟶ X.filtration.gradedPiece n :=
    cokernel.π (Subobject.ofLE _ _ (X.filtration.F_succ_le n))
  let f (n : Set.Icc a b) : X.obj ⟶ J n :=
    Injective.factorThru (q n.1) (X.filtration.F n.1).arrow
  have hf (n : Set.Icc a b) : (X.filtration.F n.1).arrow ≫ f n = q n.1 :=
    Injective.comp_factorThru _ _
  have hf_zero (p : ℤ) (n : Set.Icc a b) (hn : n.1 < p) :
      (X.filtration.F p).arrow ≫ f n = 0 := by
    have hle := X.filtration.antitone (show n.1 + 1 ≤ p by omega)
    rw [← Subobject.ofLE_arrow hle, Category.assoc,
      ← Subobject.ofLE_arrow (X.filtration.F_succ_le n.1), Category.assoc, hf]
    simp [q]
  let α (p : ℤ) : (X.filtration.F p : C) ⟶ ⨁ (tailFamily J p) :=
    biproduct.lift fun n ↦ (X.filtration.F p).arrow ≫ f n.1
  have hα (p : ℤ) (n : Tail a b p) :
      α p ≫ biproduct.π (tailFamily J p) n = (X.filtration.F p).arrow ≫ f n.1 := by
    simp [α]
  have hstep (p : ℤ) :
      Subobject.ofLE _ _ (X.filtration.F_succ_le p) ≫ α p =
        α (p + 1) ≫ tailInclusion J p := by
    apply biproduct.hom_ext
    intro n
    rw [Category.assoc, hα, ← Category.assoc, Subobject.ofLE_arrow]
    by_cases hn : p + 1 ≤ n.1.1
    · let m : Tail a b (p + 1) := ⟨n.1, hn⟩
      have hι : tailInclusion J p ≫ biproduct.π (tailFamily J p) n =
          biproduct.π (tailFamily J (p + 1)) m := by
        apply biproduct.hom_ext'
        intro k
        simp only [tailInclusion, biproduct.ι_desc_assoc, biproduct.ι_π]
        split_ifs with h₁ h₂ h₂
        · rfl
        · exact False.elim (h₂ (Subtype.ext
            (congrArg (fun x : Tail a b p ↦ x.1) h₁)))
        · exact False.elim (h₁ (Subtype.ext
            (congrArg (fun x : Tail a b (p + 1) ↦ x.1) h₂)))
        · rfl
      rw [Category.assoc, hι, hα]
    · have hι : tailInclusion J p ≫ biproduct.π (tailFamily J p) n = 0 := by
        apply biproduct.hom_ext'
        intro k
        simp only [tailInclusion, biproduct.ι_desc_assoc, comp_zero]
        apply biproduct.ι_π_ne
        intro h
        have hval := congrArg (fun x : Tail a b p ↦ x.1.1) h
        change k.1.1 = n.1.1 at hval
        exact hn (hval ▸ k.2)
      rw [Category.assoc, hι, comp_zero, hf_zero _ _ (by omega)]
  have hiso (p : ℤ) (hp : p ≤ b + 1) (hap : a ≤ p) : IsIso (α p) := by
    induction p, hp using Int.leInductionDown with
    | base =>
      have hz : IsZero (X.filtration.F (b + 1) : C) := by
        rw [hb]
        exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
      have hz' : IsZero (⨁ (tailFamily J (b + 1))) := by
        rw [IsZero.iff_id_eq_zero]
        apply biproduct.hom_ext
        intro n
        have := n.1.2.2
        have := n.2
        omega
      exact hz.isIso hz' _
    | pred p hp ih =>
      obtain ⟨n, rfl⟩ : ∃ n : ℤ, n + 1 = p := ⟨p - 1, by omega⟩
      simp only [add_sub_cancel_right] at hap
      have hi := ih (show a ≤ n + 1 by omega)
      have hn : a ≤ n ∧ n ≤ b := by omega
      let S := ShortComplex.mk
        (Subobject.ofLE _ _ (X.filtration.F_succ_le n)) (q n) (cokernel.condition _)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
      have hT := tail_shortExact J n hn
      let φ : S ⟶ tailComplex J n hn :=
        { τ₁ := α (n + 1)
          τ₂ := α n
          τ₃ := 𝟙 (J ⟨n, hn⟩)
          comm₁₂ := (hstep n).symm
          comm₂₃ := by
            change α n ≫ biproduct.π (tailFamily J n) ⟨⟨n, hn⟩, le_rfl⟩ =
              q n ≫ 𝟙 (J ⟨n, hn⟩)
            rw [hα n ⟨⟨n, hn⟩, le_rfl⟩, hf ⟨n, hn⟩, Category.comp_id] }
      have hi' : IsIso (α n) := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS hT
      exact (congrArg (fun k : ℤ ↦ IsIso (α k)) (show n + 1 - 1 = n by omega)).mpr hi'
  have hfull (p : ℤ) (hp : p ≤ a) :
      IsIso (biproduct.fromSubtype J (fun n ↦ p ≤ n.1)) := by
    refine ⟨⟨biproduct.toSubtype J _, biproduct.fromSubtype_toSubtype J _, ?_⟩⟩
    rw [biproduct.toSubtype_fromSubtype]
    apply biproduct.hom_ext
    intro n
    simp [show p ≤ n.1 from le_trans hp n.2.1]
  let β : X.obj ⟶ ⨁ J := biproduct.lift f
  have hβ (p : ℤ) : (X.filtration.F p).arrow ≫ β =
      α p ≫ biproduct.fromSubtype J (fun n ↦ p ≤ n.1) := by
    apply biproduct.hom_ext
    intro n
    simp only [Category.assoc, β, biproduct.lift_π, biproduct.fromSubtype_π]
    by_cases hn : p ≤ n.1
    · rw [dif_pos hn]
      exact (hα p ⟨n, hn⟩).symm
    · rw [dif_neg hn, comp_zero, hf_zero _ _ (by omega)]
  have ha' : IsIso (X.filtration.F a).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).mpr ha
  have := hiso a (by omega) le_rfl
  have := hfull a le_rfl
  have hβiso : IsIso ((X.filtration.F a).arrow ≫ β) := by
    rw [hβ]
    infer_instance
  have : IsIso β := by
    have h : β = inv (X.filtration.F a).arrow ≫
        ((X.filtration.F a).arrow ≫ β) := by simp
    rw [h]
    infer_instance
  refine ⟨J, hgr, fun n ↦ ⟨Iso.refl _⟩, asIso β, ?_⟩
  intro p
  change (Subobject.map β).obj (X.filtration.F p) = _
  rw [← Subobject.mk_arrow (X.filtration.F p), Subobject.map_mk,
    ← imageSubobject_mono]
  change imageSubobject ((X.filtration.F p).arrow ≫ β) =
    imageSubobject (biproduct.fromSubtype J (fun n ↦ p ≤ n.1))
  by_cases hpa : p < a
  · have hFp : X.filtration.F p = ⊤ :=
      top_unique (ha ▸ X.filtration.antitone (show p ≤ a by omega))
    have hsource : IsIso (X.filtration.F p).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).mpr hFp
    have htail := hfull p (by omega)
    rw [imageSubobject_mono, Subobject.mk_eq_top_of_isIso,
      imageSubobject_mono, Subobject.mk_eq_top_of_isIso]
  · by_cases hpb : p ≤ b + 1
    · have := hiso p hpb (by omega)
      calc
        _ = imageSubobject (α p ≫ biproduct.fromSubtype J (fun n ↦ p ≤ n.1)) := by
          congr 1
          exact hβ p
        _ = _ := imageSubobject_comp_eq_of_epi _ _
    · have hzero : biproduct.fromSubtype J (fun n ↦ p ≤ n.1) = 0 := by
        apply biproduct.hom_ext'
        intro n
        have := n.1.2.2
        have := n.2
        omega
      have hz : (X.filtration.F p).arrow ≫ β = 0 := by
        rw [hβ, hzero, comp_zero]
      simp only [hz, hzero, imageSubobject_zero]

end CategoryTheory.FilteredObject
