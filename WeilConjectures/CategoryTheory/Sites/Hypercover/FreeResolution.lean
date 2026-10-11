/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
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

/-- **The free resolution of a hypercover, positive degrees.** Let `U` be a hypercover of a
terminal object. Every cycle of degree `n + 1` of the complex `ℤ[U_•]` of free abelian presheaves
is locally a boundary. Equivalently, the sheafified complex is exact in degree `n + 1`.
(blueprint: `lem-weil-pbc-hypercover-free-resolution`) -/
theorem IsHypercover.freeComplex_locallyExact (hU : (U.augmentOfIsTerminal hT).IsHypercover J)
    (n : ℕ) {W : C} (z : ((freeComplex U).X (n + 1)).obj (op W))
    (hz : ((freeComplex U).d (n + 1) n).app (op W) z = 0) :
    ∃ R ∈ J W, ∀ ⦃W' : C⦄ (g : W' ⟶ W), R g →
      ∃ b : ((freeComplex U).X (n + 2)).obj (op W'),
        ((freeComplex U).d (n + 2) (n + 1)).app (op W') b =
          ((freeComplex U).X (n + 1)).map g.op z := by
  classical
  let z' : ULift.{w} (W ⟶ U _⦋n + 1⦌) →₀ ℤ := z
  let A : Set (W ⟶ U _⦋n + 1⦌) :=
    (fun σ : ULift.{w} (W ⟶ U _⦋n + 1⦌) ↦ σ.down) '' (↑z'.support : Set _)
  refine ⟨coneSieve (U.faceClosure A) (n + 2),
    hU.coneSieve_mem _ (U.faceClosure_δ A)
      (fun m ↦ U.faceClosure_finite (z'.support.finite_toSet.image _) m) _,
    fun W' g ⟨v, h, hc⟩ ↦ ⟨Finsupp.mapDomain (fun σ ↦ ULift.up (h (n + 1) σ.down)) z', ?_⟩⟩
  have key := U.chainBoundary_cone_succ g n (h (n + 1)) (h n) z'
    (fun σ hσ ↦ hc.δ_zero (by omega) (U.subset_faceClosure A ⟨σ, hσ, rfl⟩))
    (fun σ hσ i ↦ hc.δ_succ (by omega) (U.subset_faceClosure A ⟨σ, hσ, rfl⟩) i)
  rw [freeComplex_d_app] at hz
  change U.chainBoundary W n z' = 0 at hz
  rw [hz, Finsupp.mapDomain_zero, add_zero] at key
  exact (U.freeComplex_d_app (n + 1) W' _).trans key

/-- **The free resolution of a hypercover, degree `0`.** Let `U` be a hypercover of a terminal
object `T`. Every chain of `ℤ[U_0]` in the kernel of the augmentation `ℤ[U_0] → ℤ[T]` is locally
a boundary. (blueprint: `lem-weil-pbc-hypercover-free-resolution`) -/
theorem IsHypercover.freeComplex_locallyExact_zero
    (hU : (U.augmentOfIsTerminal hT).IsHypercover J) {W : C}
    (z : ((freeComplex U).X 0).obj (op W))
    (hz : (freeFunctor.map (hT.from (U _⦋0⦌))).app (op W) z = 0) :
    ∃ R ∈ J W, ∀ ⦃W' : C⦄ (g : W' ⟶ W), R g →
      ∃ b : ((freeComplex U).X 1).obj (op W'),
        ((freeComplex U).d 1 0).app (op W') b = ((freeComplex U).X 0).map g.op z := by
  classical
  let z' : ULift.{w} (W ⟶ U _⦋0⦌) →₀ ℤ := z
  have haug : aug (U _⦋0⦌) W z' = 0 := by
    rw [← aug_mapDomain_comp (hT.from (U _⦋0⦌))]
    exact (congrArg (aug T W) hz).trans (map_zero _)
  let A : Set (W ⟶ U _⦋0⦌) :=
    (fun σ : ULift.{w} (W ⟶ U _⦋0⦌) ↦ σ.down) '' (↑z'.support : Set _)
  refine ⟨coneSieve (U.faceClosure A) 1,
    hU.coneSieve_mem _ (U.faceClosure_δ A)
      (fun m ↦ U.faceClosure_finite (z'.support.finite_toSet.image _) m) _,
    fun W' g ⟨v, h, hc⟩ ↦ ⟨Finsupp.mapDomain (fun σ ↦ ULift.up (h 0 σ.down)) z', ?_⟩⟩
  have key := U.chainBoundary_cone_zero g v (h 0) z'
    (fun σ hσ ↦ hc.δ_zero (by omega) (U.subset_faceClosure A ⟨σ, hσ, rfl⟩))
    (fun σ hσ ↦ hc.δ_one (by omega) (U.subset_faceClosure A ⟨σ, hσ, rfl⟩))
  rw [haug, Finsupp.single_zero, sub_zero] at key
  exact (U.freeComplex_d_app 0 W' _).trans key

/-- The augmentation `ℤ[U_0] → ℤ[T]` of a hypercover of a terminal object `T` is locally
surjective. (blueprint: `lem-weil-pbc-hypercover-free-resolution`) -/
theorem IsHypercover.freeAugmentation_locallySurjective
    (hU : (U.augmentOfIsTerminal hT).IsHypercover J) {W : C}
    (z : (freeFunctor.obj T).obj (op W)) :
    ∃ R ∈ J W, ∀ ⦃W' : C⦄ (g : W' ⟶ W), R g →
      ∃ b : ((freeComplex U).X 0).obj (op W'),
        (freeFunctor.map (hT.from (U _⦋0⦌))).app (op W') b = (freeFunctor.obj T).map g.op z := by
  refine ⟨_, hU.liftSieveZero_mem (hT.from W), fun W' g ⟨y, _⟩ ↦
    ⟨Finsupp.single (ULift.up y) (aug T W z), ?_⟩⟩
  have key (x : ULift.{w} (W' ⟶ T) →₀ ℤ) (p : ULift.{w} (W' ⟶ T)) : x p = aug T W' x := by
    rw [aug, Finsupp.liftAddHom_apply, Finsupp.sum_eq_single p
      (fun b _ hb ↦ absurd (ULift.ext _ _ (hT.hom_ext _ _)) hb) (fun _ ↦ rfl)]
    rfl
  change (Finsupp.mapDomain (fun σ ↦ ULift.up (σ.down ≫ hT.from (U _⦋0⦌)))
      (Finsupp.single (ULift.up y) (aug T W z)) : ULift.{w} (W' ⟶ T) →₀ ℤ) =
    Finsupp.mapDomain (fun σ ↦ ULift.up (g ≫ σ.down)) z
  refine Finsupp.ext fun p ↦ ?_
  rw [key, key _ p, Finsupp.mapDomain_single, InjectiveCocycle.aug_mapDomain]
  simp [aug]

end Augmented

end SimplicialObject

namespace Presheaf

/-- In an abelian category, a morphism `φ : P ⟶ I` to an injective object extends along
`f : P ⟶ Q` as soon as it vanishes on the kernel of `f`. -/
lemma _root_.CategoryTheory.Injective.exists_comp_eq_of_kernel_ι_comp {𝒜 : Type*}
    [Category* 𝒜] [Abelian 𝒜] {P Q I : 𝒜} [Injective I] (f : P ⟶ Q) (φ : P ⟶ I)
    (h : kernel.ι f ≫ φ = 0) : ∃ b : Q ⟶ I, f ≫ b = φ := by
  have hf : kernel.ι (Abelian.factorThruImage f) ≫ f = 0 := by
    calc kernel.ι (Abelian.factorThruImage f) ≫ f =
        kernel.ι (Abelian.factorThruImage f) ≫ Abelian.factorThruImage f ≫ Abelian.image.ι f := by
          rw [Abelian.image.fac]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
  have hk : kernel.ι (Abelian.factorThruImage f) ≫ φ = 0 := by
    rw [← kernel.lift_ι f _ hf, Category.assoc, h, comp_zero]
  refine ⟨Injective.factorThru (Abelian.epiDesc _ φ hk) (Abelian.image.ι f), ?_⟩
  calc f ≫ Injective.factorThru (Abelian.epiDesc _ φ hk) (Abelian.image.ι f) =
      (Abelian.factorThruImage f ≫ Abelian.image.ι f) ≫
        Injective.factorThru (Abelian.epiDesc _ φ hk) (Abelian.image.ι f) := by
          rw [Abelian.image.fac]
    _ = φ := by rw [Category.assoc, Injective.comp_factorThru, Abelian.comp_epiDesc]

/-- A morphism `φ : P ⟶ I` to an injective presheaf extends along `f : P ⟶ Q` as soon as it
vanishes on the kernel of `f`. -/
lemma exists_comp_eq_of_injective {P Q I : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}} [Injective I]
    (f : P ⟶ Q) (φ : P ⟶ I) (h : ∀ W (y : P.obj W), f.app W y = 0 → φ.app W y = 0) :
    ∃ b : Q ⟶ I, f ≫ b = φ := by
  refine Injective.exists_comp_eq_of_kernel_ι_comp f φ ?_
  ext W x
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (kernel.condition f) W) x
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, NatTrans.app_zero] at h1 ⊢
  exact (h W _ h1).trans (by simp)

end Presheaf

namespace Sheaf

variable {J : GrothendieckTopology C}

/-- A section of an abelian sheaf which vanishes locally is zero. -/
lemma eq_zero_of_locally_eq_zero (F : Sheaf J AddCommGrpCat.{s}) {W : C}
    (x : F.obj.obj (op W)) (R : Sieve W) (hR : R ∈ J W)
    (h : ∀ ⦃W' : C⦄ (g : W' ⟶ W), R g → F.obj.map g.op x = 0) : x = 0 := by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (CategoryTheory.forget AddCommGrpCat) F.property)
  refine (this R hR).isSeparatedFor.ext fun W' g hg ↦ ?_
  change F.obj.map g.op x = F.obj.map g.op 0
  rw [h g hg, map_zero]

end Sheaf

namespace SimplicialObject.Augmented

open Presheaf

variable {J : GrothendieckTopology C} {U : SimplicialObject C} {T : C} {hT : IsTerminal T}
  [HasSheafify J AddCommGrpCat.{max w v}]

/-- For a hypercover `U` of a terminal object and an injective abelian sheaf `I`, the complex
`C^•(U, I)` is exact in positive degrees: every cocycle of degree `n + 1` is a coboundary.
(blueprint: `lem-weil-pbc-hypercover-free-resolution`) -/
theorem IsHypercover.exists_cechComplex_d_eq_of_injective
    (hU : (U.augmentOfIsTerminal hT).IsHypercover J) (I : Sheaf J AddCommGrpCat.{max w v})
    [Injective I] (n : ℕ) (c : I.obj.obj (op (U _⦋n + 1⦌)))
    (hc : (cechComplex U I.obj).d (n + 1) (n + 2) c = 0) :
    ∃ b : I.obj.obj (op (U _⦋n⦌)), (cechComplex U I.obj).d n (n + 1) b = c := by
  have : Injective I.obj := (sheafificationAdjunction J _).map_injective I inferInstance
  obtain ⟨b, hb⟩ := Presheaf.exists_comp_eq_of_injective ((freeComplex U).d (n + 1) n)
    (freeLift c) fun W y hy ↦ by
      obtain ⟨R, hR, hRb⟩ := hU.freeComplex_locallyExact n (W := W.unop) y hy
      refine Sheaf.eq_zero_of_locally_eq_zero I _ R hR fun W' g hg ↦ ?_
      obtain ⟨b, hb⟩ := hRb g hg
      have h1 := ConcreteCategory.congr_hom ((freeLift c).naturality g.op) y
      have h2 := ConcreteCategory.congr_hom
        (NatTrans.congr_app (U.freeComplex_d_comp_freeLift (n + 1) c) (op W')) b
      simp only [ConcreteCategory.comp_apply] at h1 h2
      change I.obj.map g.op ((freeLift c).app W y) = 0
      rw [← h1]
      change (freeLift c).app (op W') (((freeComplex U).X _).map g.op y) = 0
      rw [← hb]
      refine h2.trans ?_
      change (freeLift ((cechComplex U I.obj).d (n + 1) (n + 2) c)).app _ b = 0
      rw [hc, freeLift_eq_symm, map_zero]
      rfl
  refine ⟨freeHomAddEquiv _ b, (freeHomAddEquiv _).symm.injective ?_⟩
  rw [← freeLift_eq_symm, ← freeLift_eq_symm, ← U.freeComplex_d_comp_freeLift,
    freeLift_eq_symm, AddEquiv.symm_apply_apply, hb]

/-- For a hypercover `U` of a terminal object and an injective abelian sheaf `I`, the complex
`C^•(U, I)` is exact in positive degrees. (blueprint: `lem-weil-pbc-hypercover-free-resolution`)
-/
theorem IsHypercover.cechComplex_exactAt_of_injective
    (hU : (U.augmentOfIsTerminal hT).IsHypercover J) (I : Sheaf J AddCommGrpCat.{max w v})
    [Injective I] (n : ℕ) : (cechComplex U I.obj).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  exact fun c hc ↦ hU.exists_cechComplex_d_eq_of_injective I n c hc

/-- For a hypercover `U` of a terminal object `T` and an injective abelian sheaf `I`, the
`0`-cocycles of `C^•(U, I)` are the restrictions of the sections over `T`.
(blueprint: `lem-weil-pbc-hypercover-free-resolution`) -/
theorem IsHypercover.exists_eq_of_cechComplex_d_zero_of_injective
    (hU : (U.augmentOfIsTerminal hT).IsHypercover J) (I : Sheaf J AddCommGrpCat.{max w v})
    [Injective I] (c : I.obj.obj (op (U _⦋0⦌))) (hc : (cechComplex U I.obj).d 0 1 c = 0) :
    ∃ t : I.obj.obj (op T), I.obj.map (hT.from (U _⦋0⦌)).op t = c := by
  have : Injective I.obj := (sheafificationAdjunction J _).map_injective I inferInstance
  obtain ⟨b, hb⟩ := Presheaf.exists_comp_eq_of_injective (freeFunctor.map (hT.from (U _⦋0⦌)))
    (freeLift c) fun W y hy ↦ by
      obtain ⟨R, hR, hRb⟩ := hU.freeComplex_locallyExact_zero (W := W.unop) y hy
      refine Sheaf.eq_zero_of_locally_eq_zero I _ R hR fun W' g hg ↦ ?_
      obtain ⟨b, hb⟩ := hRb g hg
      have h1 := ConcreteCategory.congr_hom ((freeLift c).naturality g.op) y
      have h2 := ConcreteCategory.congr_hom
        (NatTrans.congr_app (U.freeComplex_d_comp_freeLift 0 c) (op W')) b
      simp only [ConcreteCategory.comp_apply] at h1 h2
      change I.obj.map g.op ((freeLift c).app W y) = 0
      rw [← h1]
      change (freeLift c).app (op W') (((freeComplex U).X _).map g.op y) = 0
      rw [← hb]
      refine h2.trans ?_
      rw [hc, freeLift_eq_symm, map_zero]
      rfl
  refine ⟨freeHomAddEquiv _ b, (freeHomAddEquiv _).symm.injective ?_⟩
  rw [← freeLift_eq_symm, ← freeLift_eq_symm, ← freeFunctor_map_comp_freeLift,
    freeLift_eq_symm, AddEquiv.symm_apply_apply, hb]

/-- For a hypercover `U` of a terminal object `T` and an abelian sheaf `F`, restriction of
sections along `U_0 → T` is injective. -/
theorem IsHypercover.map_injective (hU : (U.augmentOfIsTerminal hT).IsHypercover J)
    (F : Sheaf J AddCommGrpCat.{s}) :
    Function.Injective (F.obj.map (hT.from (U _⦋0⦌)).op) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  refine Sheaf.eq_zero_of_locally_eq_zero F t _ (hU.liftSieveZero_mem (hT.from T))
    fun W' g hg ↦ ?_
  obtain ⟨y, -⟩ := hg
  have hy : g = y ≫ hT.from (U _⦋0⦌) := hT.hom_ext _ _
  rw [hy, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  erw [ht]
  exact map_zero _

end SimplicialObject.Augmented

end CategoryTheory
