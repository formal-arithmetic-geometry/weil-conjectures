/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The pair category of a stage system is additive

Let `S` be a stage system over a directed preorder whose stages are preadditive and whose
transition functors are additive. Then the pair category `S.PairCategory` is preadditive: the
sum of two morphisms is computed after transporting representatives to a common stage
(`CategoryTheory.StageSystem.PairCategory.mkHom_add_mkHom`). If moreover the stages have zero
objects and binary biproducts, so does the pair category; in particular it is additive. The
stage inclusions `S.ι i` are additive, and so are the functors induced by morphisms of stage
systems whose stage functors are additive.

This is the additive part of blueprint `prop-weil-pbc-common-stage-calculus`.

## Main results

- `CategoryTheory.StageSystem.PairCategory.preadditive`: the preadditive structure.
- `CategoryTheory.StageSystem.PairCategory.hasZeroObject`,
  `CategoryTheory.StageSystem.PairCategory.hasFiniteBiproducts`: the pair category is additive.
- `CategoryTheory.StageSystem.Morphism.functor_additive`: descended functors are additive.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Category Limits ZeroObject

namespace StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  [∀ i, Preadditive (C i)] {S : StageSystem C} [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).Additive]

section tr

variable {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x : C i} {y : C j}

@[simp]
lemma tr_add (f g : (S.T hi).obj x ⟶ (S.T hj).obj y) : S.tr h (f + g) = S.tr h f + S.tr h g := by
  simp [tr]

@[simp]
lemma tr_neg (f : (S.T hi).obj x ⟶ (S.T hj).obj y) : S.tr h (-f) = -S.tr h f := by
  simp [tr]

@[simp]
lemma tr_zero : S.tr h (0 : (S.T hi).obj x ⟶ (S.T hj).obj y) = 0 := by
  simp [tr]

end tr

namespace PairCategory

variable [IsDirectedOrder I]

namespace Rep

variable {X Y : S.PairCategory}

/-- The sum of two representatives, computed after transport to a common stage. -/
noncomputable def add (r s : Rep X Y) : Rep X Y :=
  ⟨commonStage r.k s.k, r.hX.trans (le_commonStage_left _ _),
    r.hY.trans (le_commonStage_left _ _),
    S.tr (le_commonStage_left _ _) r.u + S.tr (le_commonStage_right _ _) s.u⟩

lemma add_rel {r r' s s' : Rep X Y} (hr : Rep.Rel r r') (hs : Rep.Rel s s') :
    Rep.Rel (r.add s) (r'.add s') := by
  obtain ⟨p, h₁, h₂, e⟩ := hr
  obtain ⟨q, h₃, h₄, e'⟩ := hs
  obtain ⟨a, ha₁, ha₂⟩ := exists_ge_ge p q
  obtain ⟨b, hb₁, hb₂⟩ := exists_ge_ge (commonStage r.k s.k) (commonStage r'.k s'.k)
  obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge a b
  refine ⟨m, hb₁.trans hm₂, hb₂.trans hm₂, ?_⟩
  change S.tr (n := commonStage r.k s.k) (hi := r.hX.trans (le_commonStage_left _ _))
      (hj := r.hY.trans (le_commonStage_left _ _)) (hb₁.trans hm₂) (S.tr _ r.u + S.tr _ s.u) =
    S.tr (n := commonStage r'.k s'.k) (hi := r'.hX.trans (le_commonStage_left _ _))
      (hj := r'.hY.trans (le_commonStage_left _ _)) (hb₂.trans hm₂) (S.tr _ r'.u + S.tr _ s'.u)
  rw [tr_add, tr_add, tr_tr, tr_tr, tr_tr, tr_tr]
  exact congr_arg₂ (· + ·) (rel_of_eq h₁ h₂ e (ha₁.trans hm₁))
    (rel_of_eq h₃ h₄ e' (ha₂.trans hm₁))

/-- The negative of a representative. -/
def neg (r : Rep X Y) : Rep X Y := ⟨r.k, r.hX, r.hY, -r.u⟩

omit [IsDirectedOrder I] in
lemma neg_rel {r r' : Rep X Y} (hr : Rep.Rel r r') : Rep.Rel r.neg r'.neg := by
  obtain ⟨p, h₁, h₂, e⟩ := hr
  refine ⟨p, h₁, h₂, ?_⟩
  change S.tr h₁ (-r.u) = S.tr h₂ (-r'.u)
  rw [tr_neg, tr_neg, e]

end Rep

noncomputable instance (X Y : S.PairCategory) : Add (X ⟶ Y) where
  add := Quotient.map₂ Rep.add (fun _ _ hr _ _ hs ↦ Rep.add_rel hr hs)

instance (X Y : S.PairCategory) : Neg (X ⟶ Y) where
  neg := Quotient.map Rep.neg (fun _ _ hr ↦ Rep.neg_rel hr)

noncomputable instance (X Y : S.PairCategory) : Zero (X ⟶ Y) where
  zero := mkHom (commonStage X.stage Y.stage) (le_commonStage_left _ _)
    (le_commonStage_right _ _) 0

variable {X Y Z : S.PairCategory}

/-- Addition of morphisms of the pair category is computed at any common stage (blueprint
`prop-weil-pbc-common-stage-calculus`). -/
lemma mkHom_add_mkHom {n : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n}
    (u v : X.toStage hX ⟶ Y.toStage hY) :
    mkHom n hX hY u + mkHom n hX hY v = mkHom n hX hY (u + v) := by
  change mkHom _ _ _ _ = _
  rw [mkHom_eq_mkHom_iff']
  refine ⟨commonStage n n, le_rfl, le_commonStage_left _ _, ?_⟩
  simp only [tr_add, tr_tr]

lemma neg_mkHom {n : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n} (u : X.toStage hX ⟶ Y.toStage hY) :
    -mkHom n hX hY u = mkHom n hX hY (-u) := rfl

@[simp]
lemma mkHom_zero {n : I} {hX : X.stage ≤ n} {hY : Y.stage ≤ n} :
    mkHom n hX hY (0 : X.toStage hX ⟶ Y.toStage hY) = 0 := by
  change _ = mkHom _ _ _ _
  rw [mkHom_eq_mkHom_iff']
  obtain ⟨p, h, h'⟩ := exists_ge_ge n (commonStage X.stage Y.stage)
  exact ⟨p, h, h', by simp⟩

omit [∀ i, Preadditive (C i)] [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).Additive] in
/-- Three morphisms of the pair category can be represented at a common stage. -/
lemma exists_common_stage₃ {X Y X' Y' X'' Y'' : S.PairCategory} (f : X ⟶ Y) (g : X' ⟶ Y')
    (k : X'' ⟶ Y'') :
    ∃ (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (hX' : X'.stage ≤ n)
      (hY' : Y'.stage ≤ n) (hX'' : X''.stage ≤ n) (hY'' : Y''.stage ≤ n)
      (u : X.toStage hX ⟶ Y.toStage hY) (u' : X'.toStage hX' ⟶ Y'.toStage hY')
      (u'' : X''.toStage hX'' ⟶ Y''.toStage hY''),
      f = mkHom n hX hY u ∧ g = mkHom n hX' hY' u' ∧ k = mkHom n hX'' hY'' u'' := by
  obtain ⟨n, -, hX, hY, hX', hY', u, u', rfl, rfl⟩ := exists_common_stage f g X.stage
  obtain ⟨n', hn, hX'', hY'', u'', rfl⟩ := exists_le_mkHom_eq k n
  exact ⟨n', hX.trans hn, hY.trans hn, hX'.trans hn, hY'.trans hn, hX'', hY'', S.tr hn u,
    S.tr hn u', u'', (mkHom_tr hn u).symm, (mkHom_tr hn u').symm, rfl⟩

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the morphism groups of the pair category
are abelian groups, the operations being computed after transport to a common stage. -/
noncomputable instance (X Y : S.PairCategory) : AddCommGroup (X ⟶ Y) where
  add_assoc f g k := by
    obtain ⟨n, hX, hY, -, -, -, -, u, v, w, rfl, rfl, rfl⟩ := exists_common_stage₃ f g k
    rw [mkHom_add_mkHom, mkHom_add_mkHom, mkHom_add_mkHom, mkHom_add_mkHom, add_assoc]
  zero_add f := by
    induction f using hom_induction with
    | h n hX hY u => rw [← mkHom_zero (hX := hX) (hY := hY), mkHom_add_mkHom, zero_add]
  add_zero f := by
    induction f using hom_induction with
    | h n hX hY u => rw [← mkHom_zero (hX := hX) (hY := hY), mkHom_add_mkHom, add_zero]
  neg_add_cancel f := by
    induction f using hom_induction with
    | h n hX hY u => rw [neg_mkHom, mkHom_add_mkHom, neg_add_cancel, mkHom_zero]
  add_comm f g := by
    obtain ⟨n, -, hX, hY, -, -, u, v, rfl, rfl⟩ := exists_common_stage f g X.stage
    rw [mkHom_add_mkHom, mkHom_add_mkHom, add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the pair category is preadditive. -/
noncomputable instance preadditive : Preadditive S.PairCategory where
  add_comp X Y Z f g k := by
    obtain ⟨n, hX, hY, -, -, -, hZ, u, v, w, rfl, rfl, rfl⟩ := exists_common_stage₃ f g k
    rw [mkHom_add_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom,
      mkHom_add_mkHom, Preadditive.add_comp]
  comp_add X Y Z f g k := by
    obtain ⟨n, hX, hY, -, hZ, -, -, u, v, w, rfl, rfl, rfl⟩ := exists_common_stage₃ f g k
    rw [mkHom_add_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom,
      mkHom_add_mkHom, Preadditive.comp_add]

/-- An object `(i, x)` with `x` zero is a zero object of the pair category. -/
lemma isZero_of_isZero {X : S.PairCategory} (hX : IsZero X.obj) : IsZero X := by
  have : IsZero (X.toStage (le_refl X.stage)) := Functor.map_isZero _ hX
  rw [IsZero.iff_id_eq_zero, id_eq_mkHom _ le_rfl, this.eq_of_src (𝟙 _) 0, mkHom_zero]

instance hasZeroObject [Nonempty I] [∀ i, HasZeroObject (C i)] :
    HasZeroObject S.PairCategory :=
  ⟨⟨⟨Classical.arbitrary I, 0⟩, isZero_of_isZero (isZero_zero _)⟩⟩

end PairCategory

open PairCategory

variable [IsDirectedOrder I]

instance (i : I) : (S.ι i).Additive where
  map_add {x y f g} := by
    rw [ι_map_eq le_rfl, ι_map_eq le_rfl, ι_map_eq le_rfl, Functor.map_add]
    exact (mkHom_add_mkHom _ _).symm

namespace PairCategory

section Biproducts

variable [∀ i, HasBinaryBiproducts (C i)]

/-- The biproduct of `X` and `Y`, computed at a common stage `n` as `j_n(T X ⊞ T Y)`. -/
noncomputable def binaryBicone (X Y : S.PairCategory) {n : I} (hX : X.stage ≤ n)
    (hY : Y.stage ≤ n) : BinaryBicone X Y where
  pt := (S.ι n).obj (X.toStage hX ⊞ Y.toStage hY)
  fst := (S.ι n).map biprod.fst ≫ (S.isoToStage X hX).inv
  snd := (S.ι n).map biprod.snd ≫ (S.isoToStage Y hY).inv
  inl := (S.isoToStage X hX).hom ≫ (S.ι n).map biprod.inl
  inr := (S.isoToStage Y hY).hom ≫ (S.ι n).map biprod.inr
  inl_fst := by simp [← Functor.map_comp_assoc]
  inl_snd := by simp [← Functor.map_comp_assoc]
  inr_fst := by simp [← Functor.map_comp_assoc]
  inr_snd := by simp [← Functor.map_comp_assoc]

lemma binaryBicone_total (X Y : S.PairCategory) {n : I} (hX : X.stage ≤ n) (hY : Y.stage ≤ n) :
    (binaryBicone X Y hX hY).fst ≫ (binaryBicone X Y hX hY).inl +
      (binaryBicone X Y hX hY).snd ≫ (binaryBicone X Y hX hY).inr = 𝟙 _ := by
  dsimp only [binaryBicone]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, biprod.total, Functor.map_id]

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the pair category has binary biproducts,
computed at a common stage. -/
instance hasBinaryBiproducts : HasBinaryBiproducts S.PairCategory where
  has_binary_biproduct X Y :=
    hasBinaryBiproduct_of_total (binaryBicone X Y (le_commonStage_left X.stage Y.stage)
      (le_commonStage_right _ _)) (binaryBicone_total _ _ _ _)

/-- Blueprint `prop-weil-pbc-common-stage-calculus`: the pair category is additive. -/
instance hasFiniteBiproducts [Nonempty I] [∀ i, HasZeroObject (C i)] :
    HasFiniteBiproducts S.PairCategory :=
  have : HasFiniteProducts S.PairCategory := hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

end Biproducts

end PairCategory

namespace Morphism

variable {D : I → Type u'} [∀ i, Category.{v'} (D i)] [∀ i, Preadditive (D i)]
  {S' : StageSystem D} [∀ ⦃i j : I⦄ (h : i ≤ j), (S'.T h).Additive] (F : Morphism S S')

omit [∀ ⦃i j : I⦄ (h : i ≤ j), (S.T h).Additive] [∀ ⦃i j : I⦄ (h : i ≤ j), (S'.T h).Additive]
  [IsDirectedOrder I] in
lemma mapAt_add [∀ i, (F.Φ i).Additive] {i j n : I} {hi : i ≤ n} {hj : j ≤ n} {x : C i}
    {y : C j} (u v : (S.T hi).obj x ⟶ (S.T hj).obj y) :
    F.mapAt (u + v) = F.mapAt u + F.mapAt v := by
  simp [mapAt]

/-- Blueprint `prop-weil-pbc-descent-functors`: the functor induced on pair categories by a
morphism of stage systems with additive stage functors is additive. -/
instance functor_additive [∀ i, (F.Φ i).Additive] : F.functor.Additive where
  map_add {X Y f g} := by
    obtain ⟨n, -, hX, hY, -, -, u, v, rfl, rfl⟩ := exists_common_stage f g X.stage
    rw [mkHom_add_mkHom, functor_map_mkHom, functor_map_mkHom, functor_map_mkHom,
      mkHom_add_mkHom]
    exact congrArg _ (mapAt_add F u v)

end Morphism

end StageSystem

end CategoryTheory
