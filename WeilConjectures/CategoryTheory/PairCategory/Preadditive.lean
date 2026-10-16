/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.PairCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The pair category is additive

Let `F` be a pseudofunctor from a directed preorder to categories, whose stages are preadditive
and whose transition functors are additive. Then the pair category `PairCategory F` is
preadditive: the sum of two morphisms is computed after transporting representatives to a
common stage. If moreover the stages have zero objects and binary biproducts, so does the pair
category; in particular it is additive. The stage inclusions `ι F i` are additive.

This is the additive part of blueprint `prop-weil-pbc-common-stage-calculus`.

## Main results

- `CategoryTheory.PairCategory.preadditive` : the preadditive structure.
- `CategoryTheory.PairCategory.homMk_add_homMk` : addition is computed at any common stage.
- `CategoryTheory.PairCategory.hasZeroObject`, `CategoryTheory.PairCategory.hasFiniteBiproducts` :
  the pair category is additive.
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits Pseudofunctor ZeroObject

namespace CategoryTheory.PairCategory

variable {ι : Type w} [Preorder ι] {F : Pseudofunctor (LocallyDiscrete ι) Cat.{v, u}}
  [∀ i : ι, Preadditive (F.obj ⟨i⟩)] [∀ ⦃i j : ι⦄ (h : i ≤ j), (F.transition h).Additive]

section trHom

variable {X Y : PairCategory F} {k k' : ι} (h : k ≤ k') (hX : X.idx ≤ k) (hY : Y.idx ≤ k)
  (hX' : X.idx ≤ k') (hY' : Y.idx ≤ k')

lemma trHom_add (u v : X.at_ hX ⟶ Y.at_ hY) :
    trHom h hX hY hX' hY' (u + v) = trHom h hX hY hX' hY' u + trHom h hX hY hX' hY' v := by
  simp [trHom]

lemma trHom_neg (u : X.at_ hX ⟶ Y.at_ hY) :
    trHom h hX hY hX' hY' (-u) = -trHom h hX hY hX' hY' u := by
  simp [trHom]

@[simp]
lemma trHom_zero : trHom h hX hY hX' hY' 0 = 0 := by
  simp [trHom]

end trHom

namespace Rep

variable {X Y : PairCategory F}

/-- The sum of two representatives, computed at a common stage `k`. -/
def addAt (r s : Rep X Y) (k : ι) (hr : r.stage ≤ k) (hs : s.stage ≤ k) : Rep X Y :=
  ⟨k, r.le₁.trans hr, r.le₂.trans hr,
    r.homAt k hr + (s.homAt k hs : X.at_ (r.le₁.trans hr) ⟶ Y.at_ (r.le₂.trans hr))⟩

lemma addAt_homAt (r s : Rep X Y) {k k' : ι} (hr : r.stage ≤ k) (hs : s.stage ≤ k)
    (h : k ≤ k') : (addAt r s k hr hs).homAt k' h = r.homAt k' (hr.trans h) +
      (s.homAt k' (hs.trans h) : X.at_ (r.le₁.trans (hr.trans h)) ⟶ _) := by
  change trHom h _ _ _ _ (r.homAt k hr + _) = _
  exact (trHom_add h _ _ _ _ _ _).trans
    (congrArg₂ (· + ·) (trHom_homAt r hr h) (trHom_homAt s hs h))

/-- The negative of a representative. -/
def neg (r : Rep X Y) : Rep X Y := ⟨r.stage, r.le₁, r.le₂, -r.hom⟩

lemma neg_homAt (r : Rep X Y) {k : ι} (h : r.stage ≤ k) : r.neg.homAt k h = -r.homAt k h :=
  trHom_neg _ _ _ _ _ _

variable [IsDirected ι (· ≤ ·)]

lemma addAt_rel (r s : Rep X Y) {k k' : ι} (hr : r.stage ≤ k)
    (hs : s.stage ≤ k) (hr' : r.stage ≤ k') (hs' : s.stage ≤ k') :
    addAt r s k hr hs ≈ addAt r s k' hr' hs' := by
  obtain ⟨k'', h, h'⟩ := directed_of (· ≤ ·) k k'
  exact ⟨k'', h, h', by rw [addAt_homAt, addAt_homAt]⟩

lemma addAt_rel_addAt {r r' s s' : Rep X Y} (hr : r ≈ r') (hs : s ≈ s')
    {k k' : ι} (h₁ : r.stage ≤ k) (h₂ : s.stage ≤ k) (h₁' : r'.stage ≤ k')
    (h₂' : s'.stage ≤ k') : addAt r s k h₁ h₂ ≈ addAt r' s' k' h₁' h₂' := by
  obtain ⟨k₁, a₁, b₁, e₁⟩ := hr
  obtain ⟨k₂, a₂, b₂, e₂⟩ := hs
  obtain ⟨m, hm₁, hm₂⟩ := directed_of (· ≤ ·) k₁ k₂
  obtain ⟨n, hn₁, hn₂⟩ := directed_of (· ≤ ·) m k
  obtain ⟨p, hp₁, hp₂⟩ := directed_of (· ≤ ·) n k'
  refine ⟨p, hn₂.trans hp₁, hp₂, ?_⟩
  rw [addAt_homAt, addAt_homAt, homAt_eq_of_le a₁ b₁ e₁ (hm₁.trans (hn₁.trans hp₁)),
    homAt_eq_of_le a₂ b₂ e₂ (hm₂.trans (hn₁.trans hp₁))]

lemma neg_rel_neg {r r' : Rep X Y} (hr : r ≈ r') : r.neg ≈ r'.neg := by
  obtain ⟨k, a, b, e⟩ := hr
  exact ⟨k, a, b, by rw [neg_homAt, neg_homAt, e]⟩

end Rep

variable [IsDirected ι (· ≤ ·)]

noncomputable instance (X Y : PairCategory F) : Add (X ⟶ Y) where
  add := Quotient.lift₂
    (fun r s ↦ homMk' (Rep.addAt r s _ (directed_of (· ≤ ·) r.stage s.stage).choose_spec.1
      (directed_of (· ≤ ·) r.stage s.stage).choose_spec.2))
    (fun _ _ _ _ hr hs ↦ Quotient.sound (Rep.addAt_rel_addAt hr hs _ _ _ _))

instance (X Y : PairCategory F) : Neg (X ⟶ Y) where
  neg := Quotient.map Rep.neg (fun _ _ h ↦ Rep.neg_rel_neg h)

noncomputable instance (X Y : PairCategory F) : Zero (X ⟶ Y) where
  zero := homMk (directed_of (· ≤ ·) X.idx Y.idx).choose_spec.1
    (directed_of (· ≤ ·) X.idx Y.idx).choose_spec.2 0

section

variable {X Y Z : PairCategory F}

/-- Addition is computed at any common stage. -/
lemma homMk_add_homMk {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k) (u v : X.at_ hX ⟶ Y.at_ hY) :
    homMk hX hY u + homMk hX hY v = homMk hX hY (u + v) := by
  change homMk' (Rep.addAt ⟨k, hX, hY, u⟩ ⟨k, hX, hY, v⟩ _ _ _) = _
  refine (Quotient.sound (Rep.addAt_rel (k' := k) _ _ _ _ le_rfl le_rfl)).trans ?_
  exact congrArg homMk' (Rep.mk_hom_congr
    (congrArg₂ (· + ·) (trHom_refl le_rfl hX hY u) (trHom_refl le_rfl hX hY v)))

lemma neg_homMk {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k) (u : X.at_ hX ⟶ Y.at_ hY) :
    -homMk hX hY u = homMk hX hY (-u) := rfl

@[simp]
lemma homMk_zero {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k) :
    homMk hX hY (0 : X.at_ hX ⟶ Y.at_ hY) = 0 := by
  obtain ⟨m, h₁, h₂⟩ := directed_of (· ≤ ·) k (directed_of (· ≤ ·) X.idx Y.idx).choose
  change homMk hX hY 0 = homMk (directed_of (· ≤ ·) X.idx Y.idx).choose_spec.1
    (directed_of (· ≤ ·) X.idx Y.idx).choose_spec.2 0
  exact (homMk_eq_homMk_iff' _ _ _ _ _ _).2 ⟨m, h₁, h₂, by simp⟩

end

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the morphism groups of the pair category are
abelian groups, the operations being computed after transport to a common stage. -/
noncomputable instance (X Y : PairCategory F) : AddCommGroup (X ⟶ Y) where
  add_assoc f g h := by
    obtain ⟨k, hX, hY, u, v, rfl, rfl⟩ := exists_homMk₂ f g
    obtain ⟨m, hm, hX', hY', w, rfl⟩ := exists_homMk_ge h k
    rw [← homMk_trHom hm hX hY hX' hY' u, ← homMk_trHom hm hX hY hX' hY' v,
      homMk_add_homMk, homMk_add_homMk, homMk_add_homMk, homMk_add_homMk, add_assoc]
  zero_add f := by
    obtain ⟨k, hX, hY, u, rfl⟩ := exists_rep f
    rw [← homMk_zero hX hY, homMk_add_homMk, zero_add]
  add_zero f := by
    obtain ⟨k, hX, hY, u, rfl⟩ := exists_rep f
    rw [← homMk_zero hX hY, homMk_add_homMk, add_zero]
  neg_add_cancel f := by
    obtain ⟨k, hX, hY, u, rfl⟩ := exists_rep f
    rw [neg_homMk, homMk_add_homMk, neg_add_cancel, homMk_zero]
  add_comm f g := by
    obtain ⟨k, hX, hY, u, v, rfl, rfl⟩ := exists_homMk₂ f g
    rw [homMk_add_homMk, homMk_add_homMk, add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the pair category is preadditive. -/
noncomputable instance preadditive : Preadditive (PairCategory F) where
  add_comp X Y Z f g h := by
    obtain ⟨k, hX, hY, hZ, u, v, w, rfl, rfl, rfl⟩ := exists_homMk₃ f g h
    rw [homMk_add_homMk, homMk_comp_homMk, homMk_comp_homMk, homMk_comp_homMk,
      homMk_add_homMk, Preadditive.add_comp]
  comp_add X Y Z f g h := by
    obtain ⟨k, hX, hY, hZ, u, v, w, rfl, rfl, rfl⟩ := exists_homMk₃' f g h
    rw [homMk_add_homMk, homMk_comp_homMk, homMk_comp_homMk, homMk_comp_homMk,
      homMk_add_homMk, Preadditive.comp_add]

instance (i : ι) : (incl F i).Additive where
  map_add {A B u v} := by
    change homMk (X := ⟨i, A⟩) (Y := ⟨i, B⟩) le_rfl le_rfl (_ ≫ (u + v) ≫ _) = _
    rw [Preadditive.add_comp, Preadditive.comp_add]
    exact (homMk_add_homMk _ _ _ _).symm

section ZeroObject

/-- An object `(i, A)` with `A` zero is a zero object of the pair category. -/
lemma isZero_of_isZero {X : PairCategory F} (hX : IsZero X.obj) : IsZero X := by
  have : IsZero (X.at_ (le_refl X.idx)) := Functor.map_isZero _ hX
  rw [IsZero.iff_id_eq_zero, id_eq_homMk, this.eq_of_src (𝟙 _) 0, homMk_zero]

variable [Nonempty ι] [∀ i : ι, HasZeroObject (F.obj ⟨i⟩)]

instance hasZeroObject : HasZeroObject (PairCategory F) :=
  ⟨⟨⟨Classical.arbitrary ι, 0⟩, isZero_of_isZero (isZero_zero _)⟩⟩

end ZeroObject

section Biproducts

variable [∀ i : ι, HasBinaryBiproducts (F.obj ⟨i⟩)]

/-- The biproduct of `(i, A)` and `(j, B)`, computed at a common stage `k`:
`(k, T_{k/i} A ⊞ T_{k/j} B)`. -/
noncomputable def binaryBicone (X Y : PairCategory F) {k : ι} (hX : X.idx ≤ k)
    (hY : Y.idx ≤ k) : BinaryBicone X Y where
  pt := ⟨k, X.at_ hX ⊞ Y.at_ hY⟩
  fst := homMk (X := ⟨k, X.at_ hX ⊞ Y.at_ hY⟩) le_rfl hX
    ((F.transitionId k le_rfl).hom.app _ ≫ biprod.fst)
  snd := homMk (X := ⟨k, X.at_ hX ⊞ Y.at_ hY⟩) le_rfl hY
    ((F.transitionId k le_rfl).hom.app _ ≫ biprod.snd)
  inl := homMk (Y := ⟨k, X.at_ hX ⊞ Y.at_ hY⟩) hX le_rfl
    (biprod.inl ≫ (F.transitionId k le_rfl).inv.app _)
  inr := homMk (Y := ⟨k, X.at_ hX ⊞ Y.at_ hY⟩) hY le_rfl
    (biprod.inr ≫ (F.transitionId k le_rfl).inv.app _)
  inl_fst := by
    rw [homMk_comp_homMk]
    convert homMk_id hX using 2
    simp
  inl_snd := by
    rw [homMk_comp_homMk]
    convert homMk_zero hX hY using 2
    simp
  inr_fst := by
    rw [homMk_comp_homMk]
    convert homMk_zero hY hX using 2
    simp
  inr_snd := by
    rw [homMk_comp_homMk]
    convert homMk_id hY using 2
    simp

lemma binaryBicone_total (X Y : PairCategory F) {k : ι} (hX : X.idx ≤ k) (hY : Y.idx ≤ k) :
    (binaryBicone X Y hX hY).fst ≫ (binaryBicone X Y hX hY).inl +
      (binaryBicone X Y hX hY).snd ≫ (binaryBicone X Y hX hY).inr = 𝟙 _ := by
  dsimp only [binaryBicone]
  rw [homMk_comp_homMk, homMk_comp_homMk]
  refine (homMk_add_homMk (X := (⟨k, X.at_ hX ⊞ Y.at_ hY⟩ : PairCategory F))
    (Y := (⟨k, X.at_ hX ⊞ Y.at_ hY⟩ : PairCategory F)) le_rfl le_rfl _ _).trans ?_
  convert homMk_id (X := (⟨k, X.at_ hX ⊞ Y.at_ hY⟩ : PairCategory F)) le_rfl using 2
  calc _ = (F.transitionId k le_rfl).hom.app _ ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫
        biprod.inr) ≫ (F.transitionId k le_rfl).inv.app (X.at_ hX ⊞ Y.at_ hY) := by
          simp only [Preadditive.comp_add, Preadditive.add_comp, assoc]
    _ = 𝟙 _ := by simp

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the pair category has binary biproducts,
computed at a common stage. -/
instance hasBinaryBiproducts : HasBinaryBiproducts (PairCategory F) where
  has_binary_biproduct X Y := by
    obtain ⟨k, hX, hY⟩ := directed_of (· ≤ ·) X.idx Y.idx
    exact hasBinaryBiproduct_of_total (binaryBicone X Y hX hY) (binaryBicone_total X Y hX hY)

variable [Nonempty ι] [∀ i : ι, HasZeroObject (F.obj ⟨i⟩)]

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the pair category is additive. -/
instance hasFiniteBiproducts : HasFiniteBiproducts (PairCategory F) :=
  have : HasFiniteProducts (PairCategory F) := hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

end Biproducts

end CategoryTheory.PairCategory
