/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverTotalComplexElem

/-!
# The augmentation of the total complex of a hypercover

In a concrete abelian category in which exactness can be tested on elements, we show that if
the augmented rows `0 → L^r(X) → L^r(U_0) → L^r(U_1) → ⋯` of the double complex of sections of
`L` over a hypercover `U` are exact, then the augmentation `Γ(X, L) ⟶ Tot(U, L)` induces
isomorphisms on cohomology. The proof is the staircase argument: modulo coboundaries a total
cochain whose differential vanishes in positive columns is concentrated in the column `p = 0`.
-/

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.SplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (U : SplitEtaleHypercover X)
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ)
  {FA : A → A → Type*} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [∀ X, AddCommGroup (CA X)] [∀ X Y, AddMonoidHomClass (FA X Y) (CA X) (CA Y)]
  (hA : ElementwiseAbelian A)

attribute [local instance] Abelian.hasFiniteBiproducts

section Elem

include hA

lemma totπ_totι_self (p r n : ℕ) (h : p + r = n) (y : ToType (U.dObj L p r)) :
    U.totπ L p r n h (U.totι L p r n h y) = y := by
  rw [← ConcreteCategory.comp_apply, totι_totπ, ConcreteCategory.id_apply]

lemma totπ_totι_ne (p r p' r' n : ℕ) (h : p + r = n) (h' : p' + r' = n) (hp : p ≠ p')
    (y : ToType (U.dObj L p r)) : U.totπ L p' r' n h' (U.totι L p r n h y) = 0 := by
  rw [← ConcreteCategory.comp_apply, U.totι_totπ_of_ne L p r p' r' n h h' hp]
  exact hA.zero_apply y

lemma tot_ext {n : ℕ} (x x' : ToType (U.totObj L n))
    (h : ∀ p r (hpr : p + r = n), U.totπ L p r n hpr x = U.totπ L p r n hpr x') : x = x' := by
  have key : ∀ y : ToType (U.totObj L n), y = ∑ j : TotIdx n,
      biproduct.ι (fun x : TotIdx n ↦ U.dObj L x.1.1 x.1.2) j
        (biproduct.π (fun x : TotIdx n ↦ U.dObj L x.1.1 x.1.2) j y) := by
    intro y
    have := congrArg (fun f ↦ f y) (biproduct.total (f := fun x : TotIdx n ↦ U.dObj L x.1.1 x.1.2))
    simp only [ConcreteCategory.id_apply, hA.sum_apply, ConcreteCategory.comp_apply] at this
    exact this.symm
  rw [key x, key x']
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  exact h j.1.1 j.1.2 (Finset.mem_antidiagonal.1 j.2)

lemma totD_totι_apply (a b n : ℕ) (h : a + b = n) (w : ToType (U.dObj L a b)) :
    U.totD L n (U.totι L a b n h w) =
      U.totι L (a + 1) b (n + 1) (by omega) (U.dHor L a b w) +
        ((-1 : ℤ) ^ a) • U.totι L a (b + 1) (n + 1) (by omega) (U.dVert L a b w) := by
  rw [← ConcreteCategory.comp_apply, totι_totD, hA.add_apply, hA.zsmul_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]

lemma totπ_totD_zero_apply (r : ℕ) (x : ToType (U.totObj L r)) :
    U.totπ L 0 (r + 1) (r + 1) (by omega) (U.totD L r x) =
      U.dVert L 0 r (U.totπ L 0 r r (by omega) x) := by
  rw [← ConcreteCategory.comp_apply, U.totD_totπ_zero L r r rfl, ConcreteCategory.comp_apply]

lemma totπ_totD_succ_zero_apply (p : ℕ) (x : ToType (U.totObj L p)) :
    U.totπ L (p + 1) 0 (p + 1) (by omega) (U.totD L p x) =
      U.dHor L p 0 (U.totπ L p 0 p (by omega) x) := by
  rw [← ConcreteCategory.comp_apply, U.totD_totπ_succ_zero L p p rfl, ConcreteCategory.comp_apply]

lemma totπ_totD_succ_succ_apply (p s n : ℕ) (h : p + s + 1 = n) (x : ToType (U.totObj L n)) :
    U.totπ L (p + 1) (s + 1) (n + 1) (by omega) (U.totD L n x) =
      U.dHor L p (s + 1) (U.totπ L p (s + 1) n (by omega) x) +
        ((-1 : ℤ) ^ (p + 1)) • U.dVert L (p + 1) s (U.totπ L (p + 1) s n (by omega) x) := by
  rw [← ConcreteCategory.comp_apply, U.totD_totπ_succ_succ L p s n h, hA.add_apply,
    hA.zsmul_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]

/-- The total cochain `x` is supported in the columns `p ≤ k`. -/
def SuppLE (n k : ℕ) (x : ToType (U.totObj L n)) : Prop :=
  ∀ p r (hpr : p + r = n), k < p → U.totπ L p r n hpr x = 0

omit hA in
lemma suppLE_of_le (n : ℕ) (x : ToType (U.totObj L n)) : U.SuppLE L n n x :=
  fun p r hpr hp ↦ absurd hpr (by omega)

/-- If `x` is supported in the columns `≤ k + 1`, the component of its differential in column
`k + 2` is the horizontal differential of its component in column `k + 1`. -/
lemma totπ_totD_of_suppLE (n k r : ℕ) (hkr : k + 1 + r = n + 1) (x : ToType (U.totObj L (n + 1)))
    (hx : U.SuppLE L (n + 1) (k + 1) x) :
    U.totπ L (k + 2) r (n + 2) (by omega) (U.totD L (n + 1) x) =
      U.dHor L (k + 1) r (U.totπ L (k + 1) r (n + 1) hkr x) := by
  cases r with
  | zero =>
    obtain rfl : k = n := by omega
    exact U.totπ_totD_succ_zero_apply L hA (k + 1) x
  | succ s =>
    rw [U.totπ_totD_succ_succ_apply L hA (k + 1) s (n + 1) (by omega),
      hx (k + 2) s (by omega) (by omega), map_zero, smul_zero, add_zero]


lemma totD_totD_apply (n : ℕ) (y : ToType (U.totObj L n)) :
    U.totD L (n + 1) (U.totD L n y) = 0 := by
  rw [← ConcreteCategory.comp_apply, totD_totD]
  exact hA.zero_apply y

variable (hrow : ∀ p r (s : ToType (U.dObj L (p + 1) r)), U.dHor L (p + 1) r s = 0 →
  ∃ t, U.dHor L p r t = s)

include hrow

lemma reduce_step (n k r : ℕ) (hkr : k + r = n) (x : ToType (U.totObj L (n + 1)))
    (hx : U.SuppLE L (n + 1) (k + 1) x)
    (hd : U.totπ L (k + 2) r (n + 2) (by omega) (U.totD L (n + 1) x) = 0) :
    ∃ w : ToType (U.dObj L k r),
      U.SuppLE L (n + 1) k (x - U.totD L n (U.totι L k r n hkr w)) := by
  rw [U.totπ_totD_of_suppLE L hA n k r (by omega) x hx] at hd
  obtain ⟨w, hw⟩ := hrow k r _ hd
  refine ⟨w, fun p r' hpr' hp ↦ ?_⟩
  rw [map_sub, U.totD_totι_apply L hA, map_add, map_zsmul]
  by_cases hpk : p = k + 1
  · subst hpk
    obtain rfl : r' = r := by omega
    rw [U.totπ_totι_self L hA, U.totπ_totι_ne L hA k (r' + 1) (k + 1) r' (n + 1) _ _ (by omega),
      smul_zero, add_zero, hw, sub_self]
  · rw [hx p r' hpr' (by omega), U.totπ_totι_ne L hA (k + 1) r p r' (n + 1) _ _ (by omega),
      U.totπ_totι_ne L hA k (r + 1) p r' (n + 1) _ _ (by omega), smul_zero, add_zero, sub_zero]

lemma exists_suppLE_zero (n : ℕ) (x : ToType (U.totObj L (n + 1)))
    (hd : ∀ p r (h : p + r = n + 2), 1 ≤ p → U.totπ L p r (n + 2) h (U.totD L (n + 1) x) = 0) :
    ∃ y : ToType (U.totObj L n), U.SuppLE L (n + 1) 0 (x - U.totD L n y) := by
  suffices H : ∀ j, j ≤ n + 1 → ∃ y, U.SuppLE L (n + 1) (n + 1 - j) (x - U.totD L n y) by
    simpa using H (n + 1) le_rfl
  intro j hj
  induction j with
  | zero =>
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero]
    exact U.suppLE_of_le L (n + 1) x
  | succ j ih =>
    obtain ⟨y, hy⟩ := ih (by omega)
    rw [show n + 1 - j = n - j + 1 by omega] at hy
    obtain ⟨w, hw⟩ := U.reduce_step L hA hrow n (n - j) j (by omega) (x - U.totD L n y) hy (by
      rw [map_sub, U.totD_totD_apply L hA, sub_zero]
      exact hd _ _ _ (by omega))
    refine ⟨y + U.totι L (n - j) j n (by omega) w, ?_⟩
    rw [show n + 1 - (j + 1) = n - j by omega, map_add, ← sub_sub]
    exact hw

end Elem


section Aug

include hA

lemma totAug_f_apply (n : ℕ) (z : ToType ((L.X n).obj.obj (op (⊤_ X.Etale)))) :
    (U.totAug L).f n z = U.totι L 0 n n (zero_add n) (U.resTop (L.X n) 0 z) :=
  ConcreteCategory.comp_apply _ _ _

omit hA in
lemma resTop_dVert_apply (r : ℕ) (z : ToType ((L.X r).obj.obj (op (⊤_ X.Etale)))) :
    U.dVert L 0 r (U.resTop (L.X r) 0 z) =
      U.resTop (L.X (r + 1)) 0 ((L.d r (r + 1)).hom.app (op (⊤_ X.Etale)) z) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  have e : U.resTop (L.X r) 0 ≫ U.dVert L 0 r =
      (L.d r (r + 1)).hom.app (op (⊤_ X.Etale)) ≫ U.resTop (L.X (r + 1)) 0 :=
    (L.d r (r + 1)).hom.naturality _
  rw [e]

lemma totπ_totAug_ne (n p r : ℕ) (h : p + r = n) (hp : 1 ≤ p)
    (z : ToType ((L.X n).obj.obj (op (⊤_ X.Etale)))) :
    U.totπ L p r n h ((U.totAug L).f n z) = 0 := by
  rw [totAug_f_apply U L hA]
  exact U.totπ_totι_ne L hA 0 n p r n _ h (by omega) _

lemma totπ_zero_totAug (n : ℕ) (z : ToType ((L.X n).obj.obj (op (⊤_ X.Etale)))) :
    U.totπ L 0 n n (zero_add n) ((U.totAug L).f n z) = U.resTop (L.X n) 0 z := by
  rw [totAug_f_apply U L hA, totπ_totι_self U L hA]

lemma totπ_one_totD_of_suppLE_zero (n : ℕ) (x : ToType (U.totObj L n))
    (hx : U.SuppLE L n 0 x) :
    U.totπ L 1 n (n + 1) (by omega) (U.totD L n x) =
      U.dHor L 0 n (U.totπ L 0 n n (by omega) x) := by
  cases n with
  | zero => exact U.totπ_totD_succ_zero_apply L hA 0 x
  | succ m =>
    rw [U.totπ_totD_succ_succ_apply L hA 0 m (m + 1) (by omega), hx 1 m (by omega) (by omega),
      map_zero, smul_zero, add_zero]

variable (hrow0 : ∀ r, Function.Injective (U.resTop (L.X r) 0))
  (hrow1 : ∀ r (s : ToType (U.dObj L 0 r)), U.dHor L 0 r s = 0 → ∃ t, U.resTop (L.X r) 0 t = s)

include hrow1 in
lemma exists_totAug_eq_of_suppLE_zero (n : ℕ) (x : ToType (U.totObj L n))
    (hx : U.SuppLE L n 0 x) (h1 : U.totπ L 1 n (n + 1) (by omega) (U.totD L n x) = 0) :
    ∃ z, (U.totAug L).f n z = x := by
  rw [U.totπ_one_totD_of_suppLE_zero L hA n x hx] at h1
  obtain ⟨z, hz⟩ := hrow1 n _ h1
  refine ⟨z, U.tot_ext L hA _ _ fun p r hpr ↦ ?_⟩
  by_cases hp : p = 0
  · subst hp
    obtain rfl : r = n := by omega
    rw [totπ_zero_totAug U L hA, hz]
  · rw [totπ_totAug_ne U L hA n p r hpr (by omega), hx p r hpr (by omega)]


variable (hrow : ∀ p r (s : ToType (U.dObj L (p + 1) r)), U.dHor L (p + 1) r s = 0 →
  ∃ t, U.dHor L p r t = s)

include hrow0 hrow1 hrow in
/-- If the augmented rows of the double complex are exact, the augmentation
`Γ(X, L) ⟶ Tot(U, L)` induces isomorphisms on cohomology. -/
theorem isIso_homologyMap_totAug (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (U.totAug L) n) := by
  apply hA.isIso_of_bijective
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, hz⟩ := HomologicalComplex.exists_isCls hA (gammaComplex L) n y
    have hz' := HomologicalComplex.IsCls.map _ (U.totAug L) hz
    rw [hy] at hz'
    cases n with
    | zero =>
      obtain ⟨w, hw⟩ := (HomologicalComplex.IsCls.eq_zero_iff hA _ 0 0 (by simp) hz').1 rfl
      have hw0 : (U.totAug L).f 0 z = 0 := by
        rw [← hw, HomologicalComplex.shape _ _ _ (by simp)]
        exact hA.zero_apply w
      have hz0 : z = 0 := hrow0 0 (by
        rw [map_zero, ← totπ_zero_totAug U L hA, hw0, map_zero])
      subst hz0
      exact (HomologicalComplex.IsCls.eq_zero_iff hA _ 0 0 (by simp) hz).2 ⟨0, map_zero _⟩
    | succ m =>
      obtain ⟨w, hw⟩ :=
        (HomologicalComplex.IsCls.eq_zero_iff hA _ m (m + 1) (by simp) hz').1 rfl
      obtain ⟨w', hw'supp, hw'd⟩ : ∃ w' : ToType (U.totObj L m), U.SuppLE L m 0 w' ∧
          U.totD L m w' = (U.totAug L).f (m + 1) z := by
        cases m with
        | zero => exact ⟨w, U.suppLE_of_le L 0 w, by rw [← totComplex_d]; exact hw⟩
        | succ m' =>
          obtain ⟨y0, hy0⟩ := U.exists_suppLE_zero L hA hrow m' w (fun p r h hp ↦ by
            rw [← totComplex_d]
            erw [hw]
            exact totπ_totAug_ne U L hA _ p r h hp z)
          refine ⟨(show ToType (U.totObj L (m' + 1)) from w) - U.totD L m' y0, hy0, ?_⟩
          rw [map_sub, U.totD_totD_apply L hA, sub_zero, ← totComplex_d]
          exact hw
      obtain ⟨g, hg⟩ := U.exists_totAug_eq_of_suppLE_zero L hA hrow1 m w' hw'supp (by
        rw [hw'd]
        exact totπ_totAug_ne U L hA _ 1 m _ le_rfl z)
      have key : U.resTop (L.X (m + 1)) 0 ((L.d m (m + 1)).hom.app (op (⊤_ X.Etale)) g) =
          U.resTop (L.X (m + 1)) 0 z := by
        rw [← resTop_dVert_apply, ← totπ_zero_totAug U L hA m g, hg,
          ← totπ_totD_zero_apply U L hA m w', hw'd, totπ_zero_totAug U L hA]
      exact (HomologicalComplex.IsCls.eq_zero_iff hA _ m (m + 1) (by simp) hz).2 ⟨g, hrow0 _ key⟩
  · intro y
    obtain ⟨x, hx⟩ := HomologicalComplex.exists_isCls hA (U.totComplex L) n y
    have hdx : U.totD L n x = 0 := by
      have := HomologicalComplex.IsCls.d_eq_zero hA _ (n + 1) hx
      rwa [totComplex_d] at this
    obtain ⟨x', hx'supp, hx'd, hcls⟩ : ∃ x', U.SuppLE L n 0 x' ∧ U.totD L n x' = 0 ∧
        (U.totComplex L).IsCls n y x' := by
      cases n with
      | zero => exact ⟨x, U.suppLE_of_le L 0 x, hdx, hx⟩
      | succ m =>
        obtain ⟨y0, hy0⟩ := U.exists_suppLE_zero L hA hrow m x (fun p r h _ ↦ by
          rw [hdx, map_zero])
        refine ⟨(show ToType (U.totObj L (m + 1)) from x) - U.totD L m y0, hy0,
          by rw [map_sub, hdx, U.totD_totD_apply L hA, sub_zero],
          ?_⟩
        obtain ⟨c, hc⟩ := HomologicalComplex.exists_isCls_of_d_eq_zero hA (U.totComplex L)
          (m + 1) (m + 2) (by simp) ((U.totComplex L).d m (m + 1) y0) (by
            rw [totComplex_d, totComplex_d]
            exact U.totD_totD_apply L hA _ y0)
        have hc0 : c = 0 := (HomologicalComplex.IsCls.eq_zero_iff hA _ m (m + 1) (by simp) hc).2
          ⟨y0, rfl⟩
        subst hc0
        have := HomologicalComplex.IsCls.sub (U.totComplex L) hx hc
        rwa [sub_zero, totComplex_d] at this
    obtain ⟨z, hz⟩ := U.exists_totAug_eq_of_suppLE_zero L hA hrow1 n x' hx'supp (by
      rw [hx'd]
      exact map_zero _)
    have hdz : (L.d n (n + 1)).hom.app (op (⊤_ X.Etale)) z = 0 := hrow0 (n + 1) (by
      rw [map_zero, ← resTop_dVert_apply, ← totπ_zero_totAug U L hA n z, hz,
        ← totπ_totD_zero_apply U L hA n x', hx'd, map_zero])
    obtain ⟨yz, hyz⟩ := HomologicalComplex.exists_isCls_of_d_eq_zero hA (gammaComplex L) n
      (n + 1) (by simp) z hdz
    refine ⟨yz, ?_⟩
    have := HomologicalComplex.IsCls.map _ (U.totAug L) hyz
    rw [hz] at this
    exact (HomologicalComplex.IsCls.eq_iff hA _ _ n rfl this hcls).2 ⟨0, by
      rw [map_zero, sub_self]⟩

end Aug

end AlgebraicGeometry.SplitEtaleHypercover
