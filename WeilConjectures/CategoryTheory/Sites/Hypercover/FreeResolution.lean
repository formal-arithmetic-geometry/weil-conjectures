/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Sites.Hypercover.Simplicial
public import WeilConjectures.CategoryTheory.Sites.InjectiveCocycle

/-!
# The free resolution of a hypercover

Let `(C, J)` be a site with a terminal object `T` and `U` a hypercover of `T`
(`CategoryTheory.SimplicialObject.Augmented.IsHypercover`). Write `ℤ[V]` for the free abelian
presheaf `W ↦ ℤ[W ⟶ V]`. The alternating face map complex

`⋯ → ℤ[U_2] → ℤ[U_1] → ℤ[U_0] → ℤ[T] → 0`

is *locally exact*: every cycle is, locally on its domain, a boundary. Equivalently, its
sheafification is exact. The proof is the cone construction: a cycle involves finitely many
simplices; after refining the domain, choose a vertex `v` in `U_0` and successively cone off each
of these simplices and their faces to `v`, using that compatible boundaries lift locally to
simplices. The alternating face formula gives `∂ h + h ∂ = 1` on the chains involved.

Consequently, for an injective abelian sheaf `I`, the complex `C^•(U, I)` of
`CategoryTheory.SimplicialObject.cechComplex` satisfies `H^0 = I(T)` and `H^p = 0` for `p > 0`:
a cocycle defines a morphism out of the free presheaf, which kills the cycles because they are
locally boundaries and `I` is separated, and the injectivity of `I` extends it along the
boundary map.

## Main definitions

- `CategoryTheory.Presheaf.freeFunctor`: the functor `V ↦ ℤ[V]` to presheaves of abelian groups.
- `CategoryTheory.SimplicialObject.freeComplex`: the complex `ℤ[U_•]`.

## Main statements

- `CategoryTheory.SimplicialObject.Augmented.IsHypercover.freeComplex_locallyExact`: cycles of
  `ℤ[U_•]` in positive degrees are locally boundaries.
- `CategoryTheory.SimplicialObject.Augmented.IsHypercover.freeComplex_locallyExact_zero`: the
  same in degree `0` for the augmented complex.
- `CategoryTheory.SimplicialObject.Augmented.IsHypercover.cechComplex_exactAt_of_injective`:
  `H^p(C^•(U, I)) = 0` for `p > 0` and `I` injective.
- `CategoryTheory.SimplicialObject.Augmented.IsHypercover.exists_eq_of_cechComplex_d_zero`:
  `H^0(C^•(U, I)) = I(T)` for `I` injective.
-/

@[expose] public section

universe w v s

open CategoryTheory Limits Opposite Simplicial AlgebraicTopology

namespace CategoryTheory

variable {C : Type w} [Category.{v} C]

namespace Presheaf

open InjectiveCocycle

/-- The free abelian presheaf functor `V ↦ ℤ[V]`, `ℤ[V](W) = ℤ[W ⟶ V]`. -/
@[simps obj]
noncomputable def freeFunctor : C ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) where
  obj X := free X
  map f :=
    { app W := AddCommGrpCat.ofHom
        (Finsupp.mapDomain.addMonoidHom fun g ↦ ULift.up (g.down ≫ f))
      naturality W W' h := by
        refine AddCommGrpCat.ext fun x ↦ ?_
        change Finsupp.mapDomain _ (Finsupp.mapDomain _ x) =
          Finsupp.mapDomain _ (Finsupp.mapDomain _ x)
        rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
        congr 1
        funext g
        simp }
  map_id X := by
    ext W x
    change Finsupp.mapDomain _ x = x
    convert Finsupp.mapDomain_id (v := x) using 2
    funext g
    simp
  map_comp f f' := by
    ext W x
    change Finsupp.mapDomain _ x = Finsupp.mapDomain _ (Finsupp.mapDomain _ x)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext g
    simp

lemma freeFunctor_map_app {X Y : C} (f : X ⟶ Y) (W : Cᵒᵖ)
    (x : ULift.{w} (W.unop ⟶ X) →₀ ℤ) :
    (freeFunctor.map f).app W x = Finsupp.mapDomain (fun g ↦ ULift.up (g.down ≫ f)) x :=
  rfl

lemma free_map_apply {X : C} {W W' : Cᵒᵖ} (h : W ⟶ W') (x : ULift.{w} (W.unop ⟶ X) →₀ ℤ) :
    (free X).map h x = Finsupp.mapDomain (fun g ↦ ULift.up (h.unop ≫ g.down)) x :=
  rfl

variable {P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}}

/-- The morphism `ℤ[X] ⟶ P` corresponding to a section `c ∈ P(X)`: `[g] ↦ P(g)(c)`. -/
noncomputable def freeLift {X : C} (c : P.obj (op X)) : free X ⟶ P where
  app W := AddCommGrpCat.ofHom (Finsupp.liftAddHom fun g ↦ zmultiplesHom _ (P.map g.down.op c))
  naturality W W' h := by
    refine AddCommGrpCat.ext fun x ↦ ?_
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
    | single g n =>
      change Finsupp.liftAddHom _ (Finsupp.mapDomain _ (Finsupp.single g n)) =
        P.map h (Finsupp.liftAddHom _ (Finsupp.single g n))
      simp only [Finsupp.mapDomain_single, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply,
        map_zsmul, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      rfl

@[simp]
lemma freeLift_app_single {X : C} (c : P.obj (op X)) (W : Cᵒᵖ) (g : ULift.{w} (W.unop ⟶ X))
    (n : ℤ) : (freeLift c).app W (Finsupp.single g n) = n • P.map g.down.op c := by
  change Finsupp.liftAddHom _ (Finsupp.single g n) = _
  simp

lemma freeLift_app_single_id {X : C} (c : P.obj (op X)) :
    (freeLift c).app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1) = c := by
  change Finsupp.liftAddHom _ (Finsupp.single _ 1) = _
  simp

lemma eq_freeLift {X : C} (φ : free X ⟶ P) :
    φ = freeLift (φ.app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1)) := by
  ext W x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  | single g n =>
    have e : (Finsupp.single g n : (free X).obj W) =
        n • (free X).map g.down.op (Finsupp.single (ULift.up (𝟙 X)) 1) := by
      change Finsupp.single g n = n • Finsupp.mapDomain _ (Finsupp.single _ 1)
      rw [Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]
      simp
    have h := ConcreteCategory.congr_hom (φ.naturality g.down.op)
      (Finsupp.single (ULift.up (𝟙 X)) 1)
    simp only [ConcreteCategory.comp_apply] at h
    erw [freeLift_app_single]
    rw [e, map_zsmul]
    exact congrArg _ h

/-- Morphisms `ℤ[X] ⟶ P` are the sections of `P` over `X`. -/
noncomputable def freeHomAddEquiv (X : C) : (free X ⟶ P) ≃+ P.obj (op X) where
  toFun φ := φ.app (op X) (Finsupp.single (ULift.up (𝟙 X)) 1)
  invFun c := freeLift c
  left_inv φ := (eq_freeLift φ).symm
  right_inv c := freeLift_app_single_id c
  map_add' _ _ := rfl

lemma freeLift_eq_symm {X : C} (c : P.obj (op X)) : freeLift c = (freeHomAddEquiv X).symm c :=
  rfl

lemma freeFunctor_map_comp_freeLift {X Y : C} (f : X ⟶ Y) (c : P.obj (op Y)) :
    freeFunctor.map f ≫ freeLift c = freeLift (P.map f.op c) := by
  rw [eq_freeLift (freeFunctor.map f ≫ freeLift c)]
  congr 1
  change (freeLift c).app (op X) (Finsupp.mapDomain _ (Finsupp.single _ 1)) = _
  rw [Finsupp.mapDomain_single]
  erw [freeLift_app_single]
  simp

end Presheaf

namespace SimplicialObject

open Presheaf InjectiveCocycle

variable (U : SimplicialObject C)

/-- The complex `ℤ[U_•]` of free abelian presheaves of a simplicial object `U`, with the
alternating sum of the faces as differential. -/
noncomputable def freeComplex : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) ℕ :=
  (alternatingFaceMapComplex _).obj (U ⋙ freeFunctor)

/-- The boundary map of chains `ℤ[W ⟶ U_{n+1}] → ℤ[W ⟶ U_n]`, `[σ] ↦ ∑ (-1)^i [d_i σ]`. -/
noncomputable def chainBoundary (W : C) (n : ℕ) :
    (ULift.{w} (W ⟶ U _⦋n + 1⦌) →₀ ℤ) →+ (ULift.{w} (W ⟶ U _⦋n⦌) →₀ ℤ) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    Finsupp.mapDomain.addMonoidHom fun σ ↦ ULift.up (σ.down ≫ U.δ i)

private lemma sum_apply {M N : AddCommGrpCat.{s}} {κ : Type*} (f : κ → (M ⟶ N))
    (s : Finset κ) (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  rw [← AddMonoidHom.finsetSum_apply]
  exact congr($(map_sum AddCommGrpCat.homAddEquiv f s) x)

lemma freeComplex_d_app (n : ℕ) (W : C) (z : ULift.{w} (W ⟶ U _⦋n + 1⦌) →₀ ℤ) :
    ((freeComplex U).d (n + 1) n).app (op W) z = U.chainBoundary W n z := by
  dsimp only [freeComplex]
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
    NatTrans.app_sum, sum_apply, chainBoundary, AddMonoidHom.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [NatTrans.app_zsmul]
  rfl

lemma chainBoundary_single (W : C) (n : ℕ) (σ : ULift.{w} (W ⟶ U _⦋n + 1⦌)) (a : ℤ) :
    U.chainBoundary W n (Finsupp.single σ a) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (ULift.up (σ.down ≫ U.δ i)) a := by
  simp [chainBoundary, AddMonoidHom.finsetSum_apply]

lemma chainBoundary_mapDomain {W W' : C} (g : W' ⟶ W) (n : ℕ)
    (z : ULift.{w} (W ⟶ U _⦋n + 1⦌) →₀ ℤ) :
    U.chainBoundary W' n (Finsupp.mapDomain (fun σ ↦ ULift.up (g ≫ σ.down)) z) =
      Finsupp.mapDomain (fun σ ↦ ULift.up (g ≫ σ.down)) (U.chainBoundary W n z) := by
  simp only [chainBoundary, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_finsetSum,
    Finsupp.mapDomain_smul, ← Finsupp.mapDomain_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  funext σ
  simp

lemma freeComplex_d_comp_freeLift {P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}} (n : ℕ)
    (c : P.obj (op (U _⦋n⦌))) :
    (freeComplex U).d (n + 1) n ≫ freeLift c = freeLift ((cechComplex U P).d n (n + 1) c) := by
  dsimp only [freeComplex]
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
    Preadditive.sum_comp, cechComplex_d_eq, sum_apply]
  conv_rhs => rw [freeLift_eq_symm, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change _ = (freeHomAddEquiv _).symm ((-1 : ℤ) ^ (i : ℕ) • P.map (U.δ i).op c)
  rw [map_zsmul, ← freeLift_eq_symm, Preadditive.zsmul_comp]
  congr 1
  exact freeFunctor_map_comp_freeLift _ _

/-- The augmentation `ℤ[V] → ℤ[V']` along a morphism `V ⟶ V'` preserves the sum of the
coefficients. -/
lemma aug_mapDomain_comp {X Y : C} (f : X ⟶ Y) (W : C) (z : ULift.{w} (W ⟶ X) →₀ ℤ) :
    aug Y W (Finsupp.mapDomain (fun g ↦ ULift.up (g.down ≫ f)) z) = aug X W z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [Finsupp.mapDomain_add, map_add, hx, hy]
  | single g n => simp [aug]

/-- The chain identity `∂ h + h ∂ = g^*` for a cone `h` on the simplices of a chain of positive
degree. -/
lemma chainBoundary_cone_succ {W W' : C} (g : W' ⟶ W) (k : ℕ)
    (h₁ : (W ⟶ U _⦋k + 1⦌) → (W' ⟶ U _⦋k + 2⦌)) (h₀ : (W ⟶ U _⦋k⦌) → (W' ⟶ U _⦋k + 1⦌))
    (z : ULift.{w} (W ⟶ U _⦋k + 1⦌) →₀ ℤ)
    (h0 : ∀ σ ∈ z.support, h₁ σ.down ≫ U.δ 0 = g ≫ σ.down)
    (hs : ∀ σ ∈ z.support, ∀ i : Fin (k + 2), h₁ σ.down ≫ U.δ i.succ = h₀ (σ.down ≫ U.δ i)) :
    U.chainBoundary W' (k + 1) (Finsupp.mapDomain (fun σ ↦ ULift.up (h₁ σ.down)) z) +
      Finsupp.mapDomain (fun σ ↦ ULift.up (h₀ σ.down)) (U.chainBoundary W k z) =
      Finsupp.mapDomain (fun σ ↦ ULift.up (g ≫ σ.down)) z := by
  let L : (ULift.{w} (W ⟶ U _⦋k + 1⦌) →₀ ℤ) →+ (ULift.{w} (W' ⟶ U _⦋k + 1⦌) →₀ ℤ) :=
    (U.chainBoundary W' (k + 1)).comp
      (Finsupp.mapDomain.addMonoidHom fun σ ↦ ULift.up (h₁ σ.down)) +
    (Finsupp.mapDomain.addMonoidHom fun σ ↦ ULift.up (h₀ σ.down)).comp (U.chainBoundary W k)
  let R : (ULift.{w} (W ⟶ U _⦋k + 1⦌) →₀ ℤ) →+ (ULift.{w} (W' ⟶ U _⦋k + 1⦌) →₀ ℤ) :=
    Finsupp.mapDomain.addMonoidHom fun σ ↦ ULift.up (g ≫ σ.down)
  change L z = R z
  rw [← Finsupp.sum_single z, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun σ hσ ↦ ?_
  simp only [L, R, AddMonoidHom.add_apply, AddMonoidHom.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, chainBoundary_single,
    Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_smul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one,
    neg_smul, Finset.sum_neg_distrib, h0 σ hσ, hs σ hσ]
  abel

/-- The chain identity `∂ h = g^* - [v] ε` for a cone `h` with vertex `v` on the simplices of a
chain of degree `0`. -/
lemma chainBoundary_cone_zero {W W' : C} (g : W' ⟶ W) (v : W' ⟶ U _⦋0⦌)
    (h₀ : (W ⟶ U _⦋0⦌) → (W' ⟶ U _⦋1⦌)) (z : ULift.{w} (W ⟶ U _⦋0⦌) →₀ ℤ)
    (h0 : ∀ σ ∈ z.support, h₀ σ.down ≫ U.δ 0 = g ≫ σ.down)
    (h1 : ∀ σ ∈ z.support, h₀ σ.down ≫ U.δ 1 = v) :
    U.chainBoundary W' 0 (Finsupp.mapDomain (fun σ ↦ ULift.up (h₀ σ.down)) z) =
      Finsupp.mapDomain (fun σ ↦ ULift.up (g ≫ σ.down)) z -
        Finsupp.single (ULift.up v) (aug (U _⦋0⦌) W z) := by
  let L : (ULift.{w} (W ⟶ U _⦋0⦌) →₀ ℤ) →+ (ULift.{w} (W' ⟶ U _⦋0⦌) →₀ ℤ) :=
    (U.chainBoundary W' 0).comp (Finsupp.mapDomain.addMonoidHom fun σ ↦ ULift.up (h₀ σ.down))
  let R : (ULift.{w} (W ⟶ U _⦋0⦌) →₀ ℤ) →+ (ULift.{w} (W' ⟶ U _⦋0⦌) →₀ ℤ) :=
    Finsupp.mapDomain.addMonoidHom (fun σ ↦ ULift.up (g ≫ σ.down)) -
      (Finsupp.singleAddHom (ULift.up v)).comp (aug (U _⦋0⦌) W)
  change L z = R z
  rw [← Finsupp.sum_single z, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun σ hσ ↦ ?_
  simp only [L, R, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, chainBoundary_single,
    Finsupp.singleAddHom_apply, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul]
  simp [aug, sub_eq_add_neg]
  erw [h0 σ hσ, h1 σ hσ]

section Cone

variable {U}

/-- A *cone* up to degree `k` over `g : W' ⟶ W` on a family `S` of simplices of `U` over `W`,
with vertex `v`: simplices `h σ` of one degree more, whose `0`-th face is `g ≫ σ` and whose
other faces are the cones on the faces of `σ`, the last face of the cone on a vertex being
`v`. -/
structure IsCone {W W' : C} (S : ∀ m : ℕ, Set (W ⟶ U _⦋m⦌)) (k : ℕ) (g : W' ⟶ W)
    (v : W' ⟶ U _⦋0⦌) (h : ∀ m : ℕ, (W ⟶ U _⦋m⦌) → (W' ⟶ U _⦋m + 1⦌)) : Prop where
  δ_zero ⦃m : ℕ⦄ (hm : m < k) ⦃σ : W ⟶ U _⦋m⦌⦄ (hσ : σ ∈ S m) : h m σ ≫ U.δ 0 = g ≫ σ
  δ_one (hk : 0 < k) ⦃σ : W ⟶ U _⦋0⦌⦄ (hσ : σ ∈ S 0) : h 0 σ ≫ U.δ 1 = v
  δ_succ ⦃m : ℕ⦄ (hm : m + 1 < k) ⦃σ : W ⟶ U _⦋m + 1⦌⦄ (hσ : σ ∈ S (m + 1))
    (i : Fin (m + 2)) : h (m + 1) σ ≫ U.δ i.succ = h m (σ ≫ U.δ i)

variable {W W' W'' : C} {S : ∀ m : ℕ, Set (W ⟶ U _⦋m⦌)} {k : ℕ} {g : W' ⟶ W}
  {v : W' ⟶ U _⦋0⦌} {h : ∀ m : ℕ, (W ⟶ U _⦋m⦌) → (W' ⟶ U _⦋m + 1⦌)}

lemma IsCone.comp (hc : IsCone S k g v h) (g' : W'' ⟶ W') :
    IsCone S k (g' ≫ g) (g' ≫ v) (fun m σ ↦ g' ≫ h m σ) where
  δ_zero m hm σ hσ := by simp [hc.δ_zero hm hσ]
  δ_one hk σ hσ := by simp [hc.δ_one hk hσ]
  δ_succ m hm σ hσ i := by simp [hc.δ_succ hm hσ i]

variable (S k) in
/-- The sieve of the morphisms `g : W' ⟶ W` over which there is a cone up to degree `k` on
`S`. -/
def coneSieve : Sieve W where
  arrows W' g := ∃ v h, IsCone S k g v h
  downward_closed := by
    rintro W' W'' g ⟨v, h, hc⟩ g'
    exact ⟨_, _, hc.comp g'⟩

variable (g v h) in
/-- The boundary of the next simplex of a cone: for a simplex `σ` of degree `k`, the family
`(g ≫ σ, h (d_0 σ), …, h (d_k σ))`, resp. `(g ≫ σ, v)` if `k = 0`. -/
def coneFamily : (k : ℕ) → (W ⟶ U _⦋k⦌) → Fin (k + 2) → (W' ⟶ U _⦋k⦌)
  | 0, σ => ![g ≫ σ, v]
  | k + 1, σ => Fin.cons (g ≫ σ) fun i ↦ h k (σ ≫ U.δ i)

lemma coneFamily_zero (k : ℕ) (σ : W ⟶ U _⦋k⦌) : coneFamily g v h k σ 0 = g ≫ σ := by
  cases k <;> rfl

variable {T : C} (hT : IsTerminal T)

include hT in
lemma IsCone.isMatchingFamily (hc : IsCone S k g v h)
    (hS : ∀ m σ, σ ∈ S (m + 1) → ∀ i, σ ≫ U.δ i ∈ S m) {σ : W ⟶ U _⦋k⦌} (hσ : σ ∈ S k) :
    (U.augmentOfIsTerminal hT).IsMatchingFamily k (coneFamily g v h k σ) := by
  cases k with
  | zero => exact hT.hom_ext _ _
  | succ m =>
    intro i j hij
    change coneFamily g v h (m + 1) σ j.succ ≫ U.δ i =
      coneFamily g v h (m + 1) σ i.castSucc ≫ U.δ j
    simp only [coneFamily, Fin.cons_succ]
    induction i using Fin.cases with
    | zero =>
      rw [Fin.castSucc_zero, Fin.cons_zero, hc.δ_zero (Nat.lt_succ_self m) (hS m σ hσ j),
        Category.assoc]
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j =>
        have hij' : i ≤ j := Fin.succ_le_succ_iff.mp hij
        rw [← Fin.succ_castSucc, Fin.cons_succ]
        cases m with
        | zero =>
          obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
          obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
          exact (hc.δ_one (by omega) (hS 0 σ hσ _)).trans (hc.δ_one (by omega) (hS 0 σ hσ _)).symm
        | succ m =>
          rw [hc.δ_succ (by omega) (hS _ σ hσ _), hc.δ_succ (by omega) (hS _ σ hσ _),
            Category.assoc, Category.assoc, U.δ_comp_δ hij']

variable (k) in
/-- Extension of the family `h` by `y` in degree `k`, after precomposition with `g'`. -/
def extendCone (h : ∀ m : ℕ, (W ⟶ U _⦋m⦌) → (W' ⟶ U _⦋m + 1⦌)) (g' : W'' ⟶ W')
    (y : (W ⟶ U _⦋k⦌) → (W'' ⟶ U _⦋k + 1⦌)) : ∀ m : ℕ, (W ⟶ U _⦋m⦌) → (W'' ⟶ U _⦋m + 1⦌) :=
  fun m ↦ if hm : m = k then by subst hm; exact y else fun σ ↦ g' ≫ h m σ

lemma extendCone_self (g' : W'' ⟶ W') (y : (W ⟶ U _⦋k⦌) → (W'' ⟶ U _⦋k + 1⦌)) :
    extendCone k h g' y k = y := by
  simp [extendCone]

lemma extendCone_of_ne (g' : W'' ⟶ W') (y : (W ⟶ U _⦋k⦌) → (W'' ⟶ U _⦋k + 1⦌)) {m : ℕ}
    (hm : m ≠ k) : extendCone k h g' y m = fun σ ↦ g' ≫ h m σ := by
  simp [extendCone, hm]

lemma IsCone.extend (hc : IsCone S k g v h) (g' : W'' ⟶ W')
    (y : (W ⟶ U _⦋k⦌) → (W'' ⟶ U _⦋k + 1⦌))
    (hy : ∀ σ ∈ S k, ∀ j, y σ ≫ U.δ j = g' ≫ coneFamily g v h k σ j) :
    IsCone S (k + 1) (g' ≫ g) (g' ≫ v) (extendCone k h g' y) where
  δ_zero m hm σ hσ := by
    obtain rfl | hmk := eq_or_ne m k
    · rw [extendCone_self, hy σ hσ, coneFamily_zero, Category.assoc]
    · rw [extendCone_of_ne _ _ hmk, Category.assoc, hc.δ_zero (by omega) hσ, Category.assoc]
  δ_one hk σ hσ := by
    obtain rfl | hk0 := eq_or_ne k 0
    · rw [extendCone_self, hy σ hσ]
      rfl
    · rw [extendCone_of_ne _ _ (Ne.symm hk0), Category.assoc, hc.δ_one (by omega) hσ]
  δ_succ m hm σ hσ i := by
    rw [extendCone_of_ne _ _ (show m ≠ k by omega)]
    obtain hmk | hmk := eq_or_ne (m + 1) k
    · subst hmk
      rw [extendCone_self, hy σ hσ]
      rfl
    · rw [extendCone_of_ne _ _ hmk, Category.assoc, hc.δ_succ (by omega) hσ]

end Cone

/-- The intersection of a family of sieves indexed by a set. -/
def interSieve {W : C} {ι : Type*} (s : Set ι) (R : ι → Sieve W) : Sieve W where
  arrows _ f := ∀ i ∈ s, R i f
  downward_closed hf g i hi := (R i).downward_closed (hf i hi) g

lemma interSieve_mem {J : GrothendieckTopology C} {W : C} {ι : Type*} {s : Set ι}
    (hs : s.Finite) (R : ι → Sieve W) (hR : ∀ i ∈ s, R i ∈ J W) : interSieve s R ∈ J W := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact J.superset_covering (fun _ _ _ i hi ↦ hi.elim) (J.top_mem W)
  | @insert a s _ _ ih =>
    refine J.superset_covering (fun _ f hf i hi ↦ ?_) (J.intersection_covering
      (hR a (Set.mem_insert _ _)) (ih fun i hi ↦ hR i (Set.mem_insert_of_mem _ hi)))
    obtain rfl | hi := hi
    · exact hf.1
    · exact hf.2 i hi

/-- The faces, iterated degeneracies and their composites, of a set of `n`-simplices. -/
def faceClosure {W : C} {n : ℕ} (A : Set (W ⟶ U _⦋n⦌)) (m : ℕ) : Set (W ⟶ U _⦋m⦌) :=
  {τ | ∃ σ ∈ A, ∃ θ : ⦋m⦌ ⟶ ⦋n⦌, τ = σ ≫ U.map θ.op}

lemma faceClosure_δ {W : C} {n : ℕ} (A : Set (W ⟶ U _⦋n⦌)) (m : ℕ) (τ : W ⟶ U _⦋m + 1⦌)
    (hτ : τ ∈ U.faceClosure A (m + 1)) (i : Fin (m + 2)) : τ ≫ U.δ i ∈ U.faceClosure A m := by
  obtain ⟨σ, hσ, θ, rfl⟩ := hτ
  exact ⟨σ, hσ, SimplexCategory.δ i ≫ θ, by simp [SimplicialObject.δ_def]⟩

lemma faceClosure_finite {W : C} {n : ℕ} {A : Set (W ⟶ U _⦋n⦌)} (hA : A.Finite) (m : ℕ) :
    (U.faceClosure A m).Finite :=
  (hA.image2 (fun σ (θ : ⦋m⦌ ⟶ ⦋n⦌) ↦ σ ≫ U.map θ.op) Set.finite_univ).subset
    fun _ ⟨σ, hσ, θ, e⟩ ↦ ⟨σ, hσ, θ, Set.mem_univ _, e.symm⟩

lemma subset_faceClosure {W : C} {n : ℕ} (A : Set (W ⟶ U _⦋n⦌)) : A ⊆ U.faceClosure A n :=
  fun σ hσ ↦ ⟨σ, hσ, 𝟙 _, by simp⟩

namespace Augmented

variable {J : GrothendieckTopology C} {U} {T : C} {hT : IsTerminal T}

/-- **The cone construction.** For a hypercover `U` of a terminal object and a finite family of
simplices closed under faces, cones up to any degree exist locally. -/
theorem IsHypercover.coneSieve_mem (hU : (U.augmentOfIsTerminal hT).IsHypercover J) {W : C}
    (S : ∀ m : ℕ, Set (W ⟶ U _⦋m⦌)) (hS : ∀ m σ, σ ∈ S (m + 1) → ∀ i, σ ≫ U.δ i ∈ S m)
    (hfin : ∀ m, (S m).Finite) (k : ℕ) : coneSieve S k ∈ J W := by
  induction k with
  | zero =>
    refine J.superset_covering ?_ (hU.liftSieveZero_mem (hT.from W))
    rintro W' g ⟨y, -⟩
    exact ⟨y, fun m σ ↦ g ≫ σ ≫ U.σ 0, ⟨fun _ hm ↦ (Nat.not_lt_zero _ hm).elim,
      fun hk ↦ (lt_irrefl _ hk).elim, fun _ hm ↦ (Nat.not_lt_zero _ hm).elim⟩⟩
  | succ k ih =>
    classical
    refine J.transitive ih _ fun W' g ⟨v, h, hc⟩ ↦ ?_
    refine J.superset_covering ?_ (interSieve_mem (hfin k)
      (fun σ ↦ (U.augmentOfIsTerminal hT).liftSieve (coneFamily g v h k σ))
      fun σ hσ ↦ hU.liftSieve_mem _ (hc.isMatchingFamily hT hS hσ))
    intro W'' g' hg'
    choose y hy using hg'
    refine ⟨g' ≫ v, extendCone k h g' fun σ ↦ if hσ : σ ∈ S k then y σ hσ else g' ≫ h k σ,
      hc.extend g' _ fun σ hσ j ↦ ?_⟩
    rw [dif_pos hσ]
    exact hy σ hσ j

end Augmented

end SimplicialObject

end CategoryTheory
