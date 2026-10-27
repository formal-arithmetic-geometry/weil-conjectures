module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Order.Fin.Basic
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Regrouping an ordered adjoint tower

Source: blueprint sec-smooth-purity/sk-prop-sp-composition,
prop-pur-affine-space-composition-law.proof.md, Step 2, and the extracted ordered-block
induction (blueprint: lem-pur-ordered-adjoint-tower-regrouping).

The auxiliary data and tree types only package the hypotheses and parenthesizations
of this statement. All functors, adjunctions and conjugation operations are Mathlib's.
The interval restriction is important: no reverse-direction functors are required.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory

open CategoryTheory.Functor

/-- The given interval functors, adjunctions and coherent comparisons. Equalities on the
 diagonal identify its functors with the identity, and `adj_id` requires the identity
 adjunction under those identifications. Coherence is written on components, including
 every weakly ordered quadruple. Source: blueprint composition-law proof, Step 2
 (blueprint: lem-pur-ordered-adjoint-tower-regrouping). -/
structure OrderedAdjointTowerData (r : ℕ) (C : Fin (r + 1) → Type u)
    [∀ i : Fin (r + 1), Category.{v} (C i)] where
  P : ∀ i j : Fin (r + 1), i ≤ j → C j ⥤ C i
  G : ∀ i j : Fin (r + 1), i ≤ j → C i ⥤ C j
  F : ∀ i j : Fin (r + 1), i ≤ j → C i ⥤ C j
  adj : ∀ (i j : Fin (r + 1)) (h : i ≤ j), P i j h ⊣ G i j h
  P_id : ∀ i : Fin (r + 1), P i i le_rfl = 𝟭 (C i)
  G_id : ∀ i : Fin (r + 1), G i i le_rfl = 𝟭 (C i)
  F_id : ∀ i : Fin (r + 1), F i i le_rfl = 𝟭 (C i)
  adj_id : ∀ i : Fin (r + 1), HEq (adj i i le_rfl) (Adjunction.id (C := C i))
  alpha : ∀ (i j k : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k),
    P j k hjk ⋙ P i j hij ≅ P i k (hij.trans hjk)
  phi : ∀ (i j k : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k),
    F i k (hij.trans hjk) ≅ F i j hij ⋙ F j k hjk
  alpha_assoc : ∀ (i j k l : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) (X : C l),
    (alpha i j k hij hjk).hom.app ((P k l hkl).obj X) ≫
        (alpha i k l (hij.trans hjk) hkl).hom.app X =
      (P i j hij).map ((alpha j k l hjk hkl).hom.app X) ≫
        (alpha i j l hij (hjk.trans hkl)).hom.app X
  phi_assoc : ∀ (i j k l : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) (X : C i),
    (phi i k l (hij.trans hjk) hkl).hom.app X ≫
        (F k l hkl).map ((phi i j k hij hjk).hom.app X) =
      (phi i j l hij (hjk.trans hkl)).hom.app X ≫
        (phi j k l hjk hkl).hom.app ((F i j hij).obj X)
  alpha_left_unit : ∀ (i k : Fin (r + 1)) (h : i ≤ k),
    alpha i i k le_rfl h =
      isoWhiskerLeft (P i k h) (eqToIso (P_id i)) ≪≫ (P i k h).rightUnitor
  alpha_right_unit : ∀ (i k : Fin (r + 1)) (h : i ≤ k),
    alpha i k k h le_rfl =
      isoWhiskerRight (eqToIso (P_id k)) (P i k h) ≪≫ (P i k h).leftUnitor
  phi_left_unit : ∀ (i k : Fin (r + 1)) (h : i ≤ k),
    phi i i k le_rfl h =
      (F i k h).leftUnitor.symm ≪≫ isoWhiskerRight (eqToIso (F_id i)).symm (F i k h)
  phi_right_unit : ∀ (i k : Fin (r + 1)) (h : i ≤ k),
    phi i k k h le_rfl =
      (F i k h).rightUnitor.symm ≪≫ isoWhiskerLeft (F i k h) (eqToIso (F_id k)).symm

namespace OrderedAdjointTowerData

variable {r : ℕ} {C : Fin (r + 1) → Type u} [∀ i : Fin (r + 1), Category.{v} (C i)]

/-- The specified right comparison, not an independently chosen isomorphism. The composite
 adjunction is `(adj j k).comp (adj i j)`, whose counit is the specified ordered counit.
 Source: blueprint composition-law proof, Step 2; Mathlib `conjugateIsoEquiv` and
 `Adjunction.comp` (blueprint: lem-pur-ordered-adjoint-tower-regrouping). -/
def comparison (T : OrderedAdjointTowerData r C) (i j k : Fin (r + 1))
    (hij : i ≤ j) (hjk : j ≤ k) :
    T.G i k (hij.trans hjk) ≅ T.G i j hij ⋙ T.G j k hjk :=
  conjugateIsoEquiv (T.adj i k (hij.trans hjk)) ((T.adj j k hjk).comp (T.adj i j hij))
    (T.alpha i j k hij hjk)

/-- The identity transformation on a diagonal interval, transported along the specified
 identity functor equalities. Source: blueprint composition-law proof, Step 2
 (blueprint: lem-pur-ordered-adjoint-tower-regrouping). -/
def diagonal (T : OrderedAdjointTowerData r C) (i : Fin (r + 1)) :
    T.F i i le_rfl ⟶ T.G i i le_rfl :=
  eqToHom (T.F_id i) ≫ eqToHom (T.G_id i).symm

/-- The ordered two-block operation, with exactly the comparison maps of the statement.
 Source: blueprint composition-law proof, Step 2, extracted block formula
 (blueprint: lem-pur-ordered-adjoint-tower-regrouping). -/
def join (T : OrderedAdjointTowerData r C) (i j k : Fin (r + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (a : T.F i j hij ⟶ T.G i j hij)
    (b : T.F j k hjk ⟶ T.G j k hjk) :
    T.F i k (hij.trans hjk) ⟶ T.G i k (hij.trans hjk) :=
  (T.phi i j k hij hjk).hom ≫ whiskerRight a (T.F j k hjk) ≫
    whiskerLeft (T.G i j hij) b ≫ (T.comparison i j k hij hjk).inv

/-- The actual recursive transformation `Gamma`: induction on the final level, taking
 the identity when the interval is empty and adjoining `eta` at each successor.
 The equality eliminations only identify endpoints of diagonal intervals.
 Source: blueprint composition-law proof, Step 2, ordered recurrence
 (blueprint: lem-pur-ordered-adjoint-tower-regrouping). -/
def gamma (T : OrderedAdjointTowerData r C)
    (eta : ∀ j : Fin r, T.F j.castSucc j.succ (Nat.le_succ _) ⟶
      T.G j.castSucc j.succ (Nat.le_succ _)) :
    ∀ j i : Fin (r + 1), ∀ h : i ≤ j, T.F i j h ⟶ T.G i j h :=
  Fin.induction
    (fun i h ↦ by
      have e : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero h)
      subst i
      exact T.diagonal 0)
    (fun j previous i h ↦
      if e : i = j.succ then by
        subst i
        exact T.diagonal j.succ
      else T.join i j.castSucc j.succ
        (Nat.le_of_lt_succ (Fin.lt_def.mp (lt_of_le_of_ne h e))) (Nat.le_succ _)
        (previous i (Nat.le_of_lt_succ (Fin.lt_def.mp (lt_of_le_of_ne h e)))) (eta j))

end OrderedAdjointTowerData

/-- Binary parenthesizations of consecutive adjacent edges. Empty intervals are allowed,
 so the unit cases are included; a join never permutes its two consecutive blocks.
 Source: blueprint composition-law proof, Step 2, extracted tree induction
 (blueprint: lem-pur-ordered-adjoint-tower-regrouping). -/
inductive OrderedAdjointTowerTree (r : ℕ) :
    ∀ i j : Fin (r + 1), i ≤ j → Type
  | empty (i : Fin (r + 1)) : OrderedAdjointTowerTree r i i le_rfl
  | leaf (j : Fin r) : OrderedAdjointTowerTree r j.castSucc j.succ (Nat.le_succ _)
  | join {i j k : Fin (r + 1)} {hij : i ≤ j} {hjk : j ≤ k}
      (left : OrderedAdjointTowerTree r i j hij) (right : OrderedAdjointTowerTree r j k hjk) :
      OrderedAdjointTowerTree r i k (hij.trans hjk)

/-- Evaluate the actual ordered tree by the given adjacent transformations, diagonal
 identities and specified block operation; no choice of map is involved.
 Source: blueprint composition-law proof, Step 2, extracted tree induction
 (blueprint: lem-pur-ordered-adjoint-tower-regrouping). -/
def OrderedAdjointTowerTree.eval {r : ℕ} {C : Fin (r + 1) → Type u}
    [∀ i : Fin (r + 1), Category.{v} (C i)] (T : OrderedAdjointTowerData r C)
    (eta : ∀ j : Fin r, T.F j.castSucc j.succ (Nat.le_succ _) ⟶
      T.G j.castSucc j.succ (Nat.le_succ _))
    {i j : Fin (r + 1)} {h : i ≤ j} (tree : OrderedAdjointTowerTree r i j h) :
    T.F i j h ⟶ T.G i j h :=
  match tree with
  | .empty i => T.diagonal i
  | .leaf j => eta j
  | .join left right => T.join _ _ _ _ _ (left.eval T eta) (right.eval T eta)

namespace OrderedAdjointTowerData

variable {r : ℕ} {C : Fin (r + 1) → Type u}
  [∀ i : Fin (r + 1), Category.{v} (C i)]

private theorem conjugate_right_unit {A B : Type u} [Category.{v} A] [Category.{v} B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) {I J : B ⥤ B}
    (p : I = 𝟭 B) (g : J = 𝟭 B) (a : I ⊣ J) (ha : HEq a (Adjunction.id (C := B))) :
    conjugateIsoEquiv adj (adj.comp a)
        (isoWhiskerLeft L (eqToIso p) ≪≫ L.rightUnitor) =
      R.leftUnitor.symm ≪≫ isoWhiskerRight (eqToIso g).symm R := by
  subst I
  subst J
  cases eq_of_heq ha
  apply Iso.ext
  simpa using conjugateEquiv_rightUnitor_hom adj

private theorem conjugate_left_unit {A B : Type u} [Category.{v} A] [Category.{v} B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) {I J : A ⥤ A}
    (p : I = 𝟭 A) (g : J = 𝟭 A) (a : I ⊣ J) (ha : HEq a (Adjunction.id (C := A))) :
    conjugateIsoEquiv adj (a.comp adj)
        (isoWhiskerRight (eqToIso p) L ≪≫ L.leftUnitor) =
      R.rightUnitor.symm ≪≫ isoWhiskerLeft R (eqToIso g).symm := by
  subst I
  subst J
  cases eq_of_heq ha
  apply Iso.ext
  simpa using conjugateEquiv_leftUnitor_hom adj

private theorem comparison_left_unit (T : OrderedAdjointTowerData r C)
    (i k : Fin (r + 1)) (h : i ≤ k) : T.comparison i i k le_rfl h =
      (T.G i k h).leftUnitor.symm ≪≫
        isoWhiskerRight (eqToIso (T.G_id i)).symm (T.G i k h) := by
  rw [comparison, T.alpha_left_unit]
  exact conjugate_right_unit (T.adj i k h) (T.P_id i) (T.G_id i) _ (T.adj_id i)

private theorem comparison_right_unit (T : OrderedAdjointTowerData r C)
    (i k : Fin (r + 1)) (h : i ≤ k) : T.comparison i k k h le_rfl =
      (T.G i k h).rightUnitor.symm ≪≫
        isoWhiskerLeft (T.G i k h) (eqToIso (T.G_id k)).symm := by
  rw [comparison, T.alpha_right_unit]
  exact conjugate_left_unit (T.adj i k h) (T.P_id k) (T.G_id k) _ (T.adj_id k)

private theorem comparison_assoc (T : OrderedAdjointTowerData r C)
    (i j k l : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) (X : C i) :
    (T.comparison i k l (hij.trans hjk) hkl).hom.app X ≫
        (T.G k l hkl).map ((T.comparison i j k hij hjk).hom.app X) =
      (T.comparison i j l hij (hjk.trans hkl)).hom.app X ≫
        (T.comparison j k l hjk hkl).hom.app ((T.G i j hij).obj X) := by
  have h :
      (T.comparison i k l (hij.trans hjk) hkl).hom ≫
          whiskerRight (T.comparison i j k hij hjk).hom (T.G k l hkl) =
        (T.comparison i j l hij (hjk.trans hkl)).hom ≫
          whiskerLeft (T.G i j hij) (T.comparison j k l hjk hkl).hom ≫
            (associator _ _ _).inv := by
    apply (conjugateEquiv (T.adj i l (hij.trans (hjk.trans hkl)))
      ((T.adj k l hkl).comp ((T.adj j k hjk).comp (T.adj i j hij)))).symm.injective
    rw [← Adjunction.leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm
        (T.adj k l hkl) (T.adj j k hjk) (T.adj i j hij)
        (T.adj i k (hij.trans hjk)) (T.adj i l (hij.trans (hjk.trans hkl))),
      ← Adjunction.leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm
        (T.adj k l hkl) (T.adj j k hjk) (T.adj i j hij)
        (T.adj j l (hjk.trans hkl)) (T.adj i l (hij.trans (hjk.trans hkl)))]
    simp only [Adjunction.leftAdjointCompNatTrans, comparison,
      conjugateIsoEquiv_apply_hom, Equiv.symm_apply_apply]
    ext Y
    simpa using T.alpha_assoc i j k l hij hjk hkl Y
  simpa using congr_app h X

private theorem join_left_unit_aux {A B : Type u} [Category.{v} A] [Category.{v} B]
    {F G : A ⥤ B} {I J : A ⥤ A} (p : I = 𝟭 A) (g : J = 𝟭 A) (a : F ⟶ G) :
    (F.leftUnitor.symm ≪≫ isoWhiskerRight (eqToIso p).symm F).hom ≫
        whiskerRight (eqToHom p ≫ eqToHom g.symm) F ≫ whiskerLeft J a ≫
          (G.leftUnitor.symm ≪≫ isoWhiskerRight (eqToIso g).symm G).inv = a := by
  subst I
  subst J
  ext X
  simp

private theorem join_right_unit_aux {A B : Type u} [Category.{v} A] [Category.{v} B]
    {F G : A ⥤ B} {I J : B ⥤ B} (p : I = 𝟭 B) (g : J = 𝟭 B) (a : F ⟶ G) :
    (F.rightUnitor.symm ≪≫ isoWhiskerLeft F (eqToIso p).symm).hom ≫
        whiskerRight a I ≫ whiskerLeft G (eqToHom p ≫ eqToHom g.symm) ≫
          (G.rightUnitor.symm ≪≫ isoWhiskerLeft G (eqToIso g).symm).inv = a := by
  subst I
  subst J
  ext X
  simp

private theorem join_left_unit (T : OrderedAdjointTowerData r C)
    (i k : Fin (r + 1)) (h : i ≤ k) (a : T.F i k h ⟶ T.G i k h) :
    T.join i i k le_rfl h (T.diagonal i) a = a := by
  unfold join diagonal
  rw [T.phi_left_unit, comparison_left_unit]
  exact join_left_unit_aux (T.F_id i) (T.G_id i) a

private theorem join_right_unit (T : OrderedAdjointTowerData r C)
    (i k : Fin (r + 1)) (h : i ≤ k) (a : T.F i k h ⟶ T.G i k h) :
    T.join i k k h le_rfl a (T.diagonal k) = a := by
  unfold join diagonal
  rw [T.phi_right_unit, comparison_right_unit]
  exact join_right_unit_aux (T.F_id k) (T.G_id k) a

private theorem comparison_inv_assoc (T : OrderedAdjointTowerData r C)
    (i j k l : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) (X : C i) :
    (T.G k l hkl).map ((T.comparison i j k hij hjk).inv.app X) ≫
        (T.comparison i k l (hij.trans hjk) hkl).inv.app X =
      (T.comparison j k l hjk hkl).inv.app ((T.G i j hij).obj X) ≫
        (T.comparison i j l hij (hjk.trans hkl)).inv.app X := by
  have h := T.comparison_assoc i j k l hij hjk hkl X
  apply (cancel_mono ((T.comparison i j l hij (hjk.trans hkl)).hom.app X)).1
  apply (cancel_mono ((T.comparison j k l hjk hkl).hom.app
    ((T.G i j hij).obj X))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← Category.assoc, ← h]
  simp [← Functor.map_comp, Category.assoc]

private theorem join_assoc (T : OrderedAdjointTowerData r C)
    (i j k l : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l)
    (a : T.F i j hij ⟶ T.G i j hij) (b : T.F j k hjk ⟶ T.G j k hjk)
    (d : T.F k l hkl ⟶ T.G k l hkl) :
    T.join i k l (hij.trans hjk) hkl (T.join i j k hij hjk a b) d =
      T.join i j l hij (hjk.trans hkl) a (T.join j k l hjk hkl b d) := by
  ext X
  simp only [join, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  rw [d.naturality_assoc]
  rw [comparison_inv_assoc]
  rw [← Category.assoc, T.phi_assoc]
  simp only [Category.assoc]
  have hn := (T.phi j k l hjk hkl).hom.naturality (a.app X)
  simp only [Functor.comp_map] at hn
  simp only [← reassoc_of% hn, Functor.comp_obj]

private theorem gamma_self (T : OrderedAdjointTowerData r C)
    (eta : ∀ j : Fin r, T.F j.castSucc j.succ (Nat.le_succ _) ⟶
      T.G j.castSucc j.succ (Nat.le_succ _)) (j : Fin (r + 1)) :
    T.gamma eta j j le_rfl = T.diagonal j := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j _ => simp [gamma]

private theorem gamma_succ (T : OrderedAdjointTowerData r C)
    (eta : ∀ j : Fin r, T.F j.castSucc j.succ (Nat.le_succ _) ⟶
      T.G j.castSucc j.succ (Nat.le_succ _)) (j : Fin r)
    (i : Fin (r + 1)) (h : i ≤ j.castSucc) :
    T.gamma eta j.succ i (h.trans (Nat.le_succ _)) =
      T.join i j.castSucc j.succ h (Nat.le_succ _)
        (T.gamma eta j.castSucc i h) (eta j) := by
  have hn : i ≠ j.succ := by intro e; subst i; exact Nat.not_succ_le_self _ h
  simp only [gamma, Fin.induction_succ, dif_neg hn]

private theorem gamma_block (T : OrderedAdjointTowerData r C)
    (eta : ∀ j : Fin r, T.F j.castSucc j.succ (Nat.le_succ _) ⟶
      T.G j.castSucc j.succ (Nat.le_succ _))
    (i j k : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    T.gamma eta k i (hij.trans hjk) =
      T.join i j k hij hjk (T.gamma eta j i hij) (T.gamma eta k j hjk) := by
  induction k using Fin.induction with
  | zero =>
    have ej : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero hjk)
    subst j
    rw [gamma_self, join_right_unit]
  | succ k ih =>
    by_cases e : j = k.succ
    · subst j
      rw [gamma_self, join_right_unit]
    · have hj : j ≤ k.castSucc := Nat.le_of_lt_succ (Fin.lt_def.mp (lt_of_le_of_ne hjk e))
      rw [gamma_succ T eta k i (hij.trans hj), gamma_succ T eta k j hj,
        ih hj, join_assoc]

private theorem gamma_leaf (T : OrderedAdjointTowerData r C)
    (eta : ∀ j : Fin r, T.F j.castSucc j.succ (Nat.le_succ _) ⟶
      T.G j.castSucc j.succ (Nat.le_succ _)) (j : Fin r) :
    T.gamma eta j.succ j.castSucc (Nat.le_succ _) = eta j := by
  rw [gamma_succ T eta j j.castSucc le_rfl, gamma_self, join_left_unit]

private theorem tree_eval (T : OrderedAdjointTowerData r C)
    (eta : ∀ j : Fin r, T.F j.castSucc j.succ (Nat.le_succ _) ⟶
      T.G j.castSucc j.succ (Nat.le_succ _))
    {i j : Fin (r + 1)} {h : i ≤ j} (tree : OrderedAdjointTowerTree r i j h) :
    tree.eval T eta = T.gamma eta j i h := by
  induction tree with
  | empty i => exact (gamma_self T eta i).symm
  | leaf j => exact (gamma_leaf T eta j).symm
  | join left right ihl ihr =>
    dsimp only [OrderedAdjointTowerTree.eval]
    rw [ihl, ihr]
    exact (gamma_block T eta _ _ _ _ _).symm

end OrderedAdjointTowerData

/-- Conjugate comparisons are coherent, the recursive comparisons are natural and obey
 every ordered block formula, and all ordered parenthesizations have the same value.
 No adjacent transformation is required to be invertible.

 Source: blueprint sec-smooth-purity/sk-prop-sp-composition,
 prop-pur-affine-space-composition-law.proof.md, Step 2; extracted four-step proof
 (blueprint: lem-pur-ordered-adjoint-tower-regrouping).

 Proof:
 1. Conjugate the `alpha_assoc` equality. Conjugation reverses vertical composition
 (def-weil-pbc-adjunction-conjugate); horizontal mate pasting with an identity square
 (lem-weil-pbc-mate-pasting, clause 2) identifies the whiskered conjugates. The two
 triple composite adjunctions have the same three successive hom bijections
 (def-weil-pbc-composite-adjunction), with identity associator components. This gives
 the displayed `c` pentagon. Conjugate the unitors with the identity adjunction to
 obtain both unit equations (mate-pasting, clause 4).
 2. Induct on interval length for naturality: `phi`, functorial application to the
 previous transformation, `eta` evaluated after `G`, and the inverse of `c` are
 natural. Their four squares compose. The unit equations give the adjacent value
 `Gamma_(i,i+1) = eta_i`.
 3. Induct on `k-j`, uniformly in `i,j` and the object, for the block formula. The
 case `k=j` reduces by the units. Substitute the inductive block formula into the
 recurrence at `l=k+1` and distribute `F_kl` over composition. Move `eta_k` past
 `F_kl(c_ijk.inv)` by its naturality at `c_ijk.inv`, a morphism of `C_k`.
 4. The inverse `c` pentagon replaces `c_ikl.inv` followed after the preceding step
 by `G_kl(c_ijk.inv)` with `c_ijl.inv` and `c_jkl.inv`. The `phi` pentagon and
 naturality of `phi_jkl` at `Gamma_ij` then move the `F_ij` block outward. The
 remaining bracket is exactly the recurrence for `Gamma_jl`; this proves the block
 identity. Finally induct on the tree: a leaf is the adjacent value, an empty tree
 is the identity, and the root operation is the block formula on the two induction
 hypotheses. This proves equality for every tree, without inverting any `eta` or
 `Gamma`. At `r=0` only empty intervals occur. -/
theorem orderedAdjointTower_regrouping (r : ℕ) (C : Fin (r + 1) → Type u)
    [∀ i : Fin (r + 1), Category.{v} (C i)] (T : OrderedAdjointTowerData r C)
    (eta : ∀ j : Fin r, T.F j.castSucc j.succ (Nat.le_succ _) ⟶
      T.G j.castSucc j.succ (Nat.le_succ _)) :
    (∀ (i j k l : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) (X : C i),
      (T.comparison i k l (hij.trans hjk) hkl).hom.app X ≫
          (T.G k l hkl).map ((T.comparison i j k hij hjk).hom.app X) =
        (T.comparison i j l hij (hjk.trans hkl)).hom.app X ≫
          (T.comparison j k l hjk hkl).hom.app ((T.G i j hij).obj X)) ∧
    (∀ (i k : Fin (r + 1)) (h : i ≤ k), T.comparison i i k le_rfl h =
      (T.G i k h).leftUnitor.symm ≪≫
        isoWhiskerRight (eqToIso (T.G_id i)).symm (T.G i k h)) ∧
    (∀ (i k : Fin (r + 1)) (h : i ≤ k), T.comparison i k k h le_rfl =
      (T.G i k h).rightUnitor.symm ≪≫
        isoWhiskerLeft (T.G i k h) (eqToIso (T.G_id k)).symm) ∧
    (∀ (i j : Fin (r + 1)) (h : i ≤ j) (X Y : C i) (f : X ⟶ Y),
      (T.F i j h).map f ≫ (T.gamma eta j i h).app Y =
        (T.gamma eta j i h).app X ≫ (T.G i j h).map f) ∧
    (∀ (i j k : Fin (r + 1)) (hij : i ≤ j) (hjk : j ≤ k) (X : C i),
      (T.gamma eta k i (hij.trans hjk)).app X =
        (T.phi i j k hij hjk).hom.app X ≫
          (T.F j k hjk).map ((T.gamma eta j i hij).app X) ≫
          (T.gamma eta k j hjk).app ((T.G i j hij).obj X) ≫
          (T.comparison i j k hij hjk).inv.app X) ∧
    (∀ (i j : Fin (r + 1)) (h : i ≤ j) (tree : OrderedAdjointTowerTree r i j h),
      tree.eval T eta = T.gamma eta j i h) := by
  refine ⟨T.comparison_assoc, T.comparison_left_unit, T.comparison_right_unit, ?_, ?_, ?_⟩
  · intro i j h X Y f
    exact (T.gamma eta j i h).naturality f
  · intro i j k hij hjk X
    exact congr_app (T.gamma_block eta i j k hij hjk) X
  · intro i j h tree
    exact T.tree_eval eta tree

end CategoryTheory
