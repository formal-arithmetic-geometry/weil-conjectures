/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverTotalComplexAug
public import WeilConjectures.AlgebraicGeometry.HypercoverTotalComplexMap
public import WeilConjectures.AlgebraicGeometry.EtaleSheafCofanGlue
public import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement

/-!
# The staircase argument with refinements

Let `F ⟶ L^•` be a resolution of an étale sheaf `F` (exact as a complex of sheaves). For a
finite split étale hypercover `U`, a total cochain of `Tot(U, L)` whose differential vanishes
in columns `p < n` can, after refining `U` and modulo coboundaries, be concentrated in the
column `p = n`. The local primitives which are needed exist on étale covers by exactness of
`L`, and are made global by refining `U` (`exists_refinement_solving_local_requirements`) and
gluing over the resulting finite coproducts.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

open SplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [∀ X, AddCommGroup (CA X)] [∀ X Y, AddMonoidHomClass (FA X Y) (CA X) (CA Y)]
  [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ)

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Local exactness of `L` in positive degrees: cocycles are locally coboundaries. -/
def LocallyExactPos : Prop :=
  ∀ (b : ℕ) (T : X.Etale) (s : ToType ((L.X (b + 1)).obj.obj (op T))),
    (L.d (b + 1) (b + 2)).hom.app (op T) s = 0 →
      Presheaf.imageSieve (L.d b (b + 1)).hom s ∈ X.smallEtaleTopology T

/-- A cocycle of positive degree on a term of a hypercover becomes a coboundary after
refinement. -/
lemma exists_refinement_dVert_eq (hL : LocallyExactPos L) (U : FiniteSplitEtaleHypercover X)
    (k b : ℕ) (s : ToType (U.dObj L k (b + 1))) (hs : U.dVert L k (b + 1) s = 0) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U) (t : ToType (V.dObj L k b)),
      V.dVert L k b t = resMap f (L.X (b + 1)) k s := by
  obtain ⟨V, f, hV⟩ := exists_refinement_solving_local_requirements U k 1 (fun _ ↦ Fin.last k)
    (fun _ ↦ Presheaf.imageSieve (L.d b (b + 1)).hom s) (fun _ ↦ hL b _ s hs)
  obtain ⟨l, T, ι, ⟨hι⟩, hR⟩ := hV (Fin.last k)
  have hloc : ∀ i, ∃ t : ToType ((L.X b).obj.obj (op (T i))),
      (L.d b (b + 1)).hom.app _ t = (L.X (b + 1)).obj.map (ι i ≫ f.app _).op s := by
    intro i
    have := hR 0 rfl i
    simp only [eqToHom_refl, Category.comp_id] at this
    exact this
  choose t ht using hloc
  obtain ⟨t', ht'⟩ := Scheme.Etale.exists_glue_of_isColimit ι hι (L.X b) t
  refine ⟨V, f, t', Scheme.Etale.ext_of_isColimit ι hι (L.X (b + 1)) fun i ↦ ?_⟩
  have e1 : (L.X (b + 1)).obj.map (ι i).op (V.dVert L k b t') =
      (L.d b (b + 1)).hom.app _ ((L.X b).obj.map (ι i).op t') :=
    (NatTrans.naturality_apply (L.d b (b + 1)).hom (ι i).op t').symm
  have e2 : (L.X (b + 1)).obj.map (ι i ≫ f.app _).op s =
      (L.X (b + 1)).obj.map (ι i).op (resMap f (L.X (b + 1)) k s) := by
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  rw [e1, ht' i, ht i, e2]

lemma zsmul_neg_one_pow_eq_zero {M : Type*} [AddCommGroup M] (m : ℕ) {v : M}
    (h : ((-1 : ℤ) ^ m) • v = 0) : v = 0 := by
  have := congrArg (((-1 : ℤ) ^ m) • ·) h
  simpa [smul_smul, ← pow_add, ← two_mul, pow_mul] using this

section Elem

variable (hA : ElementwiseAbelian A)
include hA

lemma totπ_totMapF_apply {U V : SplitEtaleHypercover X} (f : V.simplicial ⟶ U.simplicial)
    (p r n : ℕ) (h : p + r = n) (x : ToType (U.totObj L n)) :
    V.totπ L p r n h (totMapF L f n x) = resMap f (L.X r) p (U.totπ L p r n h x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  congr 1
  rw [totMapF, totπ, totπ, biproduct.map_π]

omit hA in
lemma totMapF_comp {U V W : SplitEtaleHypercover X} (f : V.simplicial ⟶ U.simplicial)
    (g : W.simplicial ⟶ V.simplicial) (n : ℕ) :
    totMapF L (g ≫ f) n = totMapF L f n ≫ totMapF L g n := by
  apply totObj_hom_ext
  intro p r h
  rw [totι_totMapF, ← Category.assoc, totι_totMapF, Category.assoc, totι_totMapF,
    ← Category.assoc]
  congr 1
  rw [← Functor.map_comp, ← op_comp]
  rfl

lemma totMapF_comp_apply {U V W : SplitEtaleHypercover X} (f : V.simplicial ⟶ U.simplicial)
    (g : W.simplicial ⟶ V.simplicial) (n : ℕ) (x : ToType (U.totObj L n)) :
    totMapF L (g ≫ f) n x = totMapF L g n (totMapF L f n x) := by
  rw [totMapF_comp, ConcreteCategory.comp_apply]

lemma totD_totMapF_apply {U V : SplitEtaleHypercover X} (f : V.simplicial ⟶ U.simplicial)
    (n : ℕ) (x : ToType (U.totObj L n)) :
    V.totD L n (totMapF L f n x) = totMapF L f (n + 1) (U.totD L n x) := by
  have := (totMap L f).comm n (n + 1)
  rw [totComplex_d, totComplex_d, totMap_f, totMap_f] at this
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, this]

/-- The total cochain `x` vanishes in the columns `p < k`. -/
def SuppGE (U : SplitEtaleHypercover X) (n k : ℕ) (x : ToType (U.totObj L n)) : Prop :=
  ∀ p r (hpr : p + r = n), p < k → U.totπ L p r n hpr x = 0

include hA in
lemma stair_step (hL : LocallyExactPos L) (U : FiniteSplitEtaleHypercover X) (k b m : ℕ)
    (hm : k + b = m) (x : ToType (U.totObj L (m + 1)))
    (hx : SuppGE L U.toSplitEtaleHypercover (m + 1) k x)
    (hd : U.totπ L k (b + 2) (m + 2) (by omega) (U.totD L (m + 1) x) = 0) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U) (y : ToType (V.totObj L m)),
      SuppGE L V.toSplitEtaleHypercover (m + 1) (k + 1) (totMapF L f (m + 1) x - V.totD L m y) := by
  have hdv : U.dVert L k (b + 1) (U.totπ L k (b + 1) (m + 1) (by omega) x) = 0 := by
    cases k with
    | zero =>
      obtain rfl : m = b := by omega
      rwa [U.totπ_totD_zero_apply L hA] at hd
    | succ k' =>
      rw [U.totπ_totD_succ_succ_apply L hA k' (b + 1) (m + 1) (by omega),
        hx k' (b + 2) (by omega) (by omega), map_zero, zero_add] at hd
      exact zsmul_neg_one_pow_eq_zero _ hd
  obtain ⟨V, f, t, ht⟩ := exists_refinement_dVert_eq L hL U k b _ hdv
  refine ⟨V, f, ((-1 : ℤ) ^ k) • V.totι L k b m hm t, fun p r hpr hp ↦ ?_⟩
  rw [map_sub, totπ_totMapF_apply L hA, map_zsmul, V.totD_totι_apply L hA, map_zsmul, map_add,
    map_zsmul]
  by_cases hpk : p = k
  · subst hpk
    obtain rfl : r = b + 1 := by omega
    rw [V.totπ_totι_ne L hA (p + 1) b p (b + 1) (m + 1) _ _ (by omega), V.totπ_totι_self L hA,
      ← ht, zero_add, smul_smul, ← pow_add, ← two_mul, pow_mul]
    simp
  · rw [hx p r hpr (by omega), map_zero,
      V.totπ_totι_ne L hA (k + 1) b p r (m + 1) _ _ (by omega),
      V.totπ_totι_ne L hA k (b + 1) p r (m + 1) _ _ (by omega)]
    simp


lemma staircase (hL : LocallyExactPos L) (U : FiniteSplitEtaleHypercover X) (m : ℕ)
    (x : ToType (U.totObj L (m + 1)))
    (hD : ∀ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U) (k b : ℕ) (hkb : k + b = m),
      V.totπ L k (b + 2) (m + 2) (by omega) (totMapF L f (m + 2) (U.totD L (m + 1) x)) = 0) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U) (y : ToType (V.totObj L m)),
      SuppGE L V.toSplitEtaleHypercover (m + 1) (m + 1)
        (totMapF L f (m + 1) x - V.totD L m y) := by
  suffices H : ∀ j, j ≤ m + 1 → ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (y : ToType (V.totObj L m)),
      SuppGE L V.toSplitEtaleHypercover (m + 1) j (totMapF L f (m + 1) x - V.totD L m y) from
    H (m + 1) le_rfl
  intro j hj
  induction j with
  | zero =>
    refine ⟨U, 𝟙 _, 0, fun p r hpr hp ↦ absurd hp (Nat.not_lt_zero _)⟩
  | succ j ih =>
    obtain ⟨V, f, y, hy⟩ := ih (by omega)
    obtain ⟨W, g, y', hy'⟩ := stair_step L hA hL V j (m - j) m (by omega) _ hy (by
      rw [map_sub, V.totD_totD_apply L hA, sub_zero, totD_totMapF_apply L hA]
      exact hD V f j (m - j) (by omega))
    refine ⟨W, g ≫ f, totMapF L g m y + y', ?_⟩
    rw [totMapF_comp_apply L hA, map_add, ← sub_sub, totD_totMapF_apply L hA, ← map_sub]
    exact hy'


section Row

variable {F : Sheaf X.smallEtaleTopology A} (ι : F ⟶ L.X 0) (hι : ι ≫ L.d 0 1 = 0)

omit hA in
lemma ι_dHor (U : SplitEtaleHypercover X) (n : ℕ) :
    ι.hom.app (op (U.simplicial _⦋n⦌)) ≫ U.dHor L n 0 =
      (U.secComplex F).d n (n + 1) ≫ ι.hom.app (op (U.simplicial _⦋n + 1⦌)) :=
  ((AlgebraicTopology.alternatingCofaceMapComplex A).map
    (Functor.whiskerLeft U.simplicial.rightOp ι.hom)).comm n (n + 1)

lemma totRow_f_apply (U : SplitEtaleHypercover X) (n : ℕ) (w : ToType ((U.secComplex F).X n)) :
    (U.totRow ι hι).f n w = U.totι L n 0 n (add_zero n) (ι.hom.app _ w) := by
  rw [show (U.totRow ι hι).f n = ι.hom.app (op (U.simplicial _⦋n⦌)) ≫
      U.totι L n 0 n (add_zero n) from rfl, ConcreteCategory.comp_apply]
  rfl

lemma totπ_totRow_self (U : SplitEtaleHypercover X) (n : ℕ) (w : ToType ((U.secComplex F).X n)) :
    U.totπ L n 0 n (add_zero n) ((U.totRow ι hι).f n w) = ι.hom.app _ w := by
  rw [totRow_f_apply L hA, U.totπ_totι_self L hA]
  rfl

lemma totπ_totRow_ne (U : SplitEtaleHypercover X) (n p r : ℕ) (h : p + r = n) (hp : p ≠ n)
    (w : ToType ((U.secComplex F).X n)) : U.totπ L p r n h ((U.totRow ι hι).f n w) = 0 := by
  rw [totRow_f_apply L hA, U.totπ_totι_ne L hA n 0 p r n _ _ (Ne.symm hp)]

variable (hglob : ∀ (T : X.Etale) (s : ToType ((L.X 0).obj.obj (op T))),
    (L.d 0 1).hom.app (op T) s = 0 → ∃ w, ι.hom.app (op T) w = s)
  (hinj : ∀ T : X.Etale, Function.Injective (ι.hom.app (op T)))

include hglob hinj in
/-- A total cocycle concentrated in the last column comes from a cocycle of `C(U, F)`. -/
lemma exists_totRow_eq_of_suppGE (U : SplitEtaleHypercover X) (n : ℕ)
    (x : ToType (U.totObj L n)) (hx : SuppGE L U n n x) (w' : ToType ((U.secComplex F).X (n + 1)))
    (hdx : U.totD L n x = (U.totRow ι hι).f (n + 1) w') :
    ∃ w : ToType ((U.secComplex F).X n), (U.secComplex F).d n (n + 1) w = w' ∧
      (U.totRow ι hι).f n w = x := by
  have h1 : U.dVert L n 0 (U.totπ L n 0 n (by omega) x) = 0 := by
    have h0 := totπ_totRow_ne L hA ι hι U (n + 1) n 1 rfl (by omega) w'
    cases n with
    | zero =>
      have := congrArg (U.totπ L 0 1 1 rfl) hdx
      rwa [U.totπ_totD_zero_apply L hA, h0] at this
    | succ m =>
      have := congrArg (U.totπ L (m + 1) 1 (m + 2) rfl) hdx
      rw [U.totπ_totD_succ_succ_apply L hA m 0 (m + 1) rfl, hx m 1 (by omega) (by omega),
        map_zero, zero_add, h0] at this
      exact zsmul_neg_one_pow_eq_zero _ this
  obtain ⟨w, hw⟩ := hglob _ _ h1
  have h2 : U.dHor L n 0 (U.totπ L n 0 n (by omega) x) = ι.hom.app _ w' := by
    have := congrArg (U.totπ L (n + 1) 0 (n + 1) rfl) hdx
    rwa [U.totπ_totD_succ_zero_apply L hA, totπ_totRow_self L hA] at this
  refine ⟨w, hinj _ ?_, U.tot_ext L hA _ _ fun p r hpr ↦ ?_⟩
  · have e := congrArg (fun φ ↦ φ w) (ι_dHor L ι U n)
    simp only [ConcreteCategory.comp_apply] at e
    refine e.symm.trans ?_
    erw [hw]
    exact h2
  · by_cases hp : p = n
    · subst hp
      obtain rfl : r = 0 := by omega
      exact (totπ_totRow_self L hA ι hι U p w).trans hw
    · rw [totπ_totRow_ne L hA, hx p r hpr (by omega)]
      exact hp

include hglob hinj in
/-- Surjectivity on cohomology in degree `0`. -/
lemma exists_totRow_eq_zero (U : SplitEtaleHypercover X) (x : ToType (U.totObj L 0))
    (hx : U.totD L 0 x = 0) :
    ∃ w : ToType ((U.secComplex F).X 0), (U.secComplex F).d 0 1 w = 0 ∧
      (U.totRow ι hι).f 0 w = x :=
  exists_totRow_eq_of_suppGE L hA ι hι hglob hinj U 0 x (fun _ _ _ hp ↦ absurd hp (by omega)) 0
    (by rw [hx, map_zero])

include hglob hinj in
/-- Surjectivity on cohomology in positive degrees, after refinement. -/
lemma exists_refinement_totRow_eq (hL : LocallyExactPos L) (U : FiniteSplitEtaleHypercover X)
    (m : ℕ) (x : ToType (U.totObj L (m + 1))) (hx : U.totD L (m + 1) x = 0) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (w : ToType ((V.secComplex F).X (m + 1))) (y : ToType (V.totObj L m)),
      (V.secComplex F).d (m + 1) (m + 2) w = 0 ∧
        (V.totRow ι hι).f (m + 1) w = totMapF L f (m + 1) x - V.totD L m y := by
  obtain ⟨V, f, y, hy⟩ := staircase L hA hL U m x (fun V f k b hkb ↦ by
    rw [hx, map_zero, map_zero])
  obtain ⟨w, hw, hwx⟩ := exists_totRow_eq_of_suppGE L hA ι hι hglob hinj V.toSplitEtaleHypercover
    (m + 1) _ hy 0 (by
      rw [map_zero, map_sub, V.totD_totD_apply L hA, sub_zero, totD_totMapF_apply L hA, hx,
        map_zero])
  exact ⟨V, f, w, y, hw, hwx⟩

include hglob hinj in
/-- Injectivity on cohomology in degree `0`. -/
lemma eq_zero_of_totRow_eq_zero (U : SplitEtaleHypercover X) (w : ToType ((U.secComplex F).X 0))
    (hw : (U.totRow ι hι).f 0 w = 0) : w = 0 := by
  apply hinj
  rw [map_zero]
  exact (totπ_totRow_self L hA ι hι U 0 w).symm.trans (by rw [hw, map_zero])

include hglob hinj in
/-- Injectivity on cohomology in positive degrees, after refinement. -/
lemma exists_refinement_secComplex_d_eq (hL : LocallyExactPos L)
    (U : FiniteSplitEtaleHypercover X) (m : ℕ) (w : ToType ((U.secComplex F).X (m + 1)))
    (y : ToType (U.totObj L m)) (hy : U.totD L m y = (U.totRow ι hι).f (m + 1) w) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (v : ToType ((V.secComplex F).X m)),
      (V.secComplex F).d m (m + 1) v = (secMap f F).f (m + 1) w := by
  cases m with
  | zero =>
    obtain ⟨v, hv, -⟩ := exists_totRow_eq_of_suppGE L hA ι hι hglob hinj U.toSplitEtaleHypercover
      0 y (fun _ _ _ hp ↦ absurd hp (by omega)) w hy
    refine ⟨U, 𝟙 _, v, ?_⟩
    rw [hv, secMap_f]
    change w = ConcreteCategory.hom (F.obj.map (𝟙 (op (U.simplicial _⦋0 + 1⦌)))) w
    rw [F.obj.map_id, ConcreteCategory.id_apply]
  | succ m =>
    have hrow : ∀ {V : FiniteSplitEtaleHypercover X} (f : V.Refinement U),
        totMapF L f (m + 2) ((U.totRow ι hι).f (m + 2) w) =
          (V.totRow ι hι).f (m + 2) ((secMap f F).f (m + 2) w) := by
      intro V f
      have := congrArg (fun φ ↦ φ.f (m + 2) w) (totRow_totMap L f ι hι)
      simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply, totMap_f] at this
      exact this
    obtain ⟨V, f, y', hy'⟩ := staircase L hA hL U m y (fun V f k b hkb ↦ by
      rw [hy, hrow, totπ_totRow_ne L hA _ _ _ _ _ _ _ (by omega)])
    obtain ⟨v, hv, -⟩ := exists_totRow_eq_of_suppGE L hA ι hι hglob hinj V.toSplitEtaleHypercover
      (m + 1) _ hy' ((secMap f F).f (m + 2) w) (by
        rw [map_sub, V.totD_totD_apply L hA, sub_zero, totD_totMapF_apply L hA, hy, hrow])
    exact ⟨V, f, v, hv⟩

end Row

end Elem

end AlgebraicGeometry.FiniteSplitEtaleHypercover
