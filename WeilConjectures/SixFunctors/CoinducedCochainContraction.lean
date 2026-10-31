/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.SixFunctorsBasics.CochainFiniteImage
import Mathlib.Tactic.Abel

/-!
# Coinduced continuous cochain contraction

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-base-field-cd/`
`sk-lem-base-field-cd-cochains.proof.md`, Proof (1), paragraph beginning “Effaceability”.
(blueprint: `lem-sfb-coinduced-cochain-contraction`)

For a profinite group `G` and a discrete `G`-module `M`, the coinduced module
`I = Map_cont(G, M)` (here the published `DiscreteModule.coind₁`, the functions invariant under
right translation by an open subgroup, which for compact `G` are exactly the continuous maps to
the discrete `M`) receives the orbit embedding `M → I`; the homogeneous cochains of `M` and the
inhomogeneous cochains of `I` are isomorphic complexes, and insertion of `1` is a contracting
homotopy in positive degrees.

## Main statements

* `coinducedCochainContraction`: the orbit embedding, the coordinate isomorphism of complexes
  and the insertion homotopy, hence `H^s(C^•(G, I)) = 0` for `s ≥ 1`.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

universe u w

/-- The homogeneous cochains `K^r`: continuous (equivalently locally constant) maps
`G^{r+1} → M`, `M` discrete. Source: `sk-lem-base-field-cd-cochains.proof.md`, Proof (1),
paragraph beginning “Effaceability”. (blueprint: `lem-sfb-coinduced-cochain-contraction`) -/
abbrev coinducedHomogeneousCochains (G : Type u) [Group G] [TopologicalSpace G]
    (M : DiscreteModule.{w} G) (r : ℕ) :=
  LocallyConstant (Fin (r + 1) → G) M.obj.V

/-- The inhomogeneous cochains `C^r(G, I)`: continuous (equivalently locally constant) maps
`G^r → I` into the single discrete coinduced module `I = DiscreteModule.coind₁ G M`.
Source: `sk-lem-base-field-cd-cochains.proof.md`, Proof (1), paragraph beginning
“Effaceability”. (blueprint: `lem-sfb-coinduced-cochain-contraction`) -/
abbrev coinducedInhomogeneousCochains (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (M : DiscreteModule.{w} G) (r : ℕ) :=
  LocallyConstant (Fin r → G)
    ((DiscreteModule.coind₁ G).obj (AddCommGrpCat.of M.obj.V)).obj.V

/-- The coinduced discrete module `I = Map_cont(G, M)` with `(h u)(g) = u (g h)`, the published
coinduction `DiscreteModule.coind₁` applied to the underlying group of `M`. Source:
`sk-lem-base-field-cd-cochains.proof.md`, Proof (1), paragraph beginning “Effaceability”.
(blueprint: `lem-sfb-coinduced-cochain-contraction`) -/
abbrev coinducedModule (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (M : DiscreteModule.{w} G) :=
  (DiscreteModule.coind₁ G).obj (AddCommGrpCat.of M.obj.V)

/-- Omission of the `i`-th entry of a homogeneous tuple `(x_0, …, x_{r+1})`, giving
`(x_0, …, \hat{x_i}, …, x_{r+1})`. Source: `sk-lem-base-field-cd-cochains.proof.md`, Proof (1),
paragraph beginning “Effaceability”. (blueprint: `lem-sfb-coinduced-cochain-contraction`) -/
def coinducedOmit {r : ℕ} {G : Type u} (i : Fin (r + 2)) (g : Fin (r + 2) → G) :
    Fin (r + 1) → G := fun j ↦ g (i.succAbove j)

private def contractionCurry
    {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (F : LocallyConstant (X × Y) V) : LocallyConstant X (LocallyConstant Y V) where
  toFun x := ⟨fun y ↦ F (x, y),
    F.isLocallyConstant.comp_continuous (continuous_const.prodMk continuous_id)⟩
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hf₀ : IsLocallyConstant (fun p : X × Y ↦ F (x, p.2)) :=
      F.isLocallyConstant.comp_continuous (continuous_const.prodMk continuous_snd)
    have hopen : IsOpen {p : X × Y | F p = F (x, p.2)} :=
      (F.isLocallyConstant.prodMk hf₀) {p | p.1 = p.2}
    have he := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := x) (P := fun x' y ↦ F (x', y) = F (x, y))
      (fun y _ ↦ hopen.mem_nhds (by rfl))
    filter_upwards [he] with x' hx'
    exact LocallyConstant.ext (fun y ↦ hx' y (Set.mem_univ y))

private theorem contractionEvaluate
    {X Y T V : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    (F : LocallyConstant X (LocallyConstant Y V))
    (a : T → X) (b : T → Y) (ha : Continuous a) (hb : Continuous b) :
    IsLocallyConstant (fun t ↦ F (a t) (b t)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  filter_upwards [(F.isLocallyConstant.comp_continuous ha).eventually_eq t,
    ((F (a t)).isLocallyConstant.comp_continuous hb).eventually_eq t] with t' h₁ h₂
  change F (a t') = F (a t) at h₁
  change F (a t) (b t') = F (a t) (b t) at h₂
  rw [h₁, h₂]

private def contractionSmoothEquiv
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (V : Type*) [AddCommGroup V] :
    DiscreteModule.smoothFunctions G V ≃+ LocallyConstant G V where
  toFun f :=
    { toFun := f.1
      isLocallyConstant := by
        rw [IsLocallyConstant.iff_exists_open]
        intro x
        refine ⟨(fun y : G ↦ x⁻¹ * y) ⁻¹' (DiscreteModule.rightStab G f.1 : Set G),
          f.2.preimage (continuous_const_mul _), ?_, ?_⟩
        · simp
        · intro y hy
          simpa using hy x }
  invFun f := ⟨f, by
    let : TopologicalSpace V := ⊥
    let : DiscreteTopology V := ⟨rfl⟩
    obtain ⟨_, N, hN⟩ := continuous_cochain_finite_image G 1 V
      (fun g ↦ f (g 0)) (f.continuous.comp (continuous_apply 0))
    refine Subgroup.isOpen_mono (H₁ := N.toSubgroup) ?_ N.isOpen
    intro h hh x
    exact hN (fun _ ↦ x) (fun _ ↦ h) (fun _ ↦ hh)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem contractionPartialProdContinuous
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (r : ℕ) (i : Fin (r + 1)) : Continuous (fun g : Fin r → G ↦ Fin.partialProd g i) := by
  induction i using Fin.inductionOn with
  | zero => simpa using (continuous_const : Continuous (fun _ : Fin r → G ↦ (1 : G)))
  | succ i ih =>
    convert ih.mul (continuous_apply i) using 1
    funext g
    simp only [Pi.mul_apply, Fin.partialProd_succ]

private def contractionCoordinates
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : DiscreteModule.{w} G) (r : ℕ) :
    coinducedHomogeneousCochains G M r ≃+ coinducedInhomogeneousCochains G M r where
  toFun f :=
    (contractionCurry
      (⟨fun p : (Fin r → G) × G ↦ f (fun i ↦ p.2 * Fin.partialProd p.1 i),
        f.isLocallyConstant.comp_continuous (continuous_pi fun i ↦
          continuous_snd.mul ((contractionPartialProdContinuous r i).comp continuous_fst))⟩))
      |>.map (contractionSmoothEquiv G M.obj.V).symm
  invFun ψ :=
    { toFun := fun x ↦ (ψ (fun i ↦ (x i.castSucc)⁻¹ * x i.succ)).1 (x 0)
      isLocallyConstant := by
        exact contractionEvaluate (ψ.map (contractionSmoothEquiv G M.obj.V))
          (fun x : Fin (r + 1) → G ↦ fun i ↦ (x i.castSucc)⁻¹ * x i.succ)
          (fun x : Fin (r + 1) → G ↦ x 0)
          (continuous_pi fun i ↦ (continuous_apply i.castSucc).inv.mul
            (continuous_apply i.succ)) (continuous_apply 0) }
  left_inv f := by
    apply LocallyConstant.ext
    intro x
    change f (fun i ↦ x 0 * Fin.partialProd (fun j ↦ (x j.castSucc)⁻¹ * x j.succ) i) = f x
    exact congrArg f (Fin.partialProd_left_inv x)
  right_inv ψ := by
    apply LocallyConstant.ext
    intro g
    apply Subtype.ext
    funext t
    change (ψ (fun i ↦ (t * Fin.partialProd g i.castSucc)⁻¹ *
      (t * Fin.partialProd g i.succ))).1 (t * Fin.partialProd g 0) = (ψ g).1 t
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, Fin.partialProd_right_inv,
      Fin.partialProd_zero, mul_one]
  map_add' f h := by
    apply LocallyConstant.ext
    intro g
    apply Subtype.ext
    funext t
    rfl

private def contractionDifferential
    (G : Type u) [Group G] [TopologicalSpace G]
    (M : DiscreteModule.{w} G) (r : ℕ) :
    coinducedHomogeneousCochains G M r →+
      coinducedHomogeneousCochains G M (r + 1) :=
  ∑ i : Fin (r + 2), (-1 : ℤ) ^ i.val •
    LocallyConstant.comapAddMonoidHom ⟨coinducedOmit i,
      continuous_pi fun j ↦ continuous_apply (i.succAbove j)⟩

private theorem contractionDifferential_apply
    (G : Type u) [Group G] [TopologicalSpace G]
    (M : DiscreteModule.{w} G) (r : ℕ)
    (f : coinducedHomogeneousCochains G M r) (g : Fin (r + 2) → G) :
    contractionDifferential G M r f g =
      ∑ i : Fin (r + 2), (-1 : ℤ) ^ i.val • f (coinducedOmit i g) := by
  simp only [contractionDifferential, AddMonoidHom.finsetSum_apply, AddMonoidHom.zsmul_apply]
  exact map_sum (LocallyConstant.evalAddMonoidHom g) _ _

private def contractionInsertion
    (G : Type u) [Group G] [TopologicalSpace G]
    (M : DiscreteModule.{w} G) (r : ℕ) :
    coinducedHomogeneousCochains G M (r + 1) →+
      coinducedHomogeneousCochains G M r :=
  LocallyConstant.comapAddMonoidHom ⟨(fun g : Fin (r + 1) → G ↦ Fin.cons (1 : G) g), by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.cons_zero] using
        (continuous_const : Continuous (fun _ : Fin (r + 1) → G ↦ (1 : G)))
    · simpa only [Fin.cons_succ] using (continuous_apply j :
        Continuous (fun g : Fin (r + 1) → G ↦ g j))⟩

private theorem contractionInsertion_identity
    (G : Type u) [Group G] [TopologicalSpace G]
    (M : DiscreteModule.{w} G) (r : ℕ)
    (f : coinducedHomogeneousCochains G M (r + 1)) :
    contractionDifferential G M r (contractionInsertion G M r f) +
      contractionInsertion G M (r + 1) (contractionDifferential G M (r + 1) f) = f := by
  apply LocallyConstant.ext
  intro g
  change contractionDifferential G M r (contractionInsertion G M r f) g +
    contractionDifferential G M (r + 1) f (Fin.cons 1 g) = f g
  rw [contractionDifferential_apply, contractionDifferential_apply]
  rw [Fin.sum_univ_succ (fun i : Fin (r + 3) ↦
    (-1 : ℤ) ^ i.val • f (coinducedOmit i (Fin.cons 1 g)))]
  have hzero : coinducedOmit 0 (Fin.cons (1 : G) g) = g := by
    funext j
    simp [coinducedOmit]
  have hsucc (i : Fin (r + 2)) :
      coinducedOmit i.succ (Fin.cons (1 : G) g) = Fin.cons 1 (coinducedOmit i g) :=
    Fin.cons_comp_succ_succAbove 1 g i
  simp only [hzero, hsucc, Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  change (∑ i : Fin (r + 2),
      (-1 : ℤ) ^ i.val • f (Fin.cons 1 (coinducedOmit i g))) +
    (f g + ∑ i : Fin (r + 2),
      (-1 : ℤ) ^ (i.val + 1) • f (Fin.cons 1 (coinducedOmit i g))) = f g
  simp only [pow_succ', mul_zsmul, neg_one_zsmul, Finset.sum_neg_distrib]
  abel

private theorem contractionCoordinates_symm_eval
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : DiscreteModule.{w} G) (r : ℕ)
    (ψ : coinducedInhomogeneousCochains G M r) (g : Fin r → G) (t : G) :
    (contractionCoordinates G M r).symm ψ (fun i ↦ t * Fin.partialProd g i) = (ψ g).1 t := by
  exact congrArg (fun F : coinducedInhomogeneousCochains G M r ↦ (F g).1 t)
    ((contractionCoordinates G M r).apply_symm_apply ψ)

private theorem contractionCoordinates_differential
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : DiscreteModule.{w} G) (r : ℕ)
    (ψ : coinducedInhomogeneousCochains G M r) (g : Fin (r + 1) → G) :
    contractionCoordinates G M (r + 1)
        (contractionDifferential G M r ((contractionCoordinates G M r).symm ψ)) g =
      ((coinducedModule G M).obj.ρ (g 0)).hom (ψ (fun j ↦ g j.succ)) +
        ∑ i : Fin (r + 1), (-1 : ℤ) ^ (i.val + 1) •
          ψ (Fin.contractNth i (· * ·) g) := by
  apply Subtype.ext
  funext t
  change contractionDifferential G M r ((contractionCoordinates G M r).symm ψ)
    (fun i ↦ t * Fin.partialProd g i) = _
  rw [contractionDifferential_apply, Fin.sum_univ_succ]
  have hfirst : coinducedOmit 0 (fun i ↦ t * Fin.partialProd g i) =
      fun i ↦ (t * g 0) * Fin.partialProd (fun j ↦ g j.succ) i := by
    funext i
    simp only [coinducedOmit, Fin.succAbove_zero, Fin.partialProd_succ', mul_assoc]
    rfl
  have hrest (k : Fin (r + 1)) :
      coinducedOmit k.succ (fun i ↦ t * Fin.partialProd g i) =
        fun i ↦ t * Fin.partialProd (Fin.contractNth k (· * ·) g) i := by
    funext i
    rw [Fin.partialProd_contractNth]
    rfl
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, hfirst, hrest,
    contractionCoordinates_symm_eval]
  let ev : (coinducedModule G M).obj.V →+ M.obj.V :=
    { toFun := fun f ↦ f.1 t
      map_zero' := rfl
      map_add' _ _ := rfl }
  change (ψ (fun j ↦ g j.succ)).1 (t * g 0) +
      (∑ i : Fin (r + 1), (-1 : ℤ) ^ (i.val + 1) •
        (ψ (Fin.contractNth i (· * ·) g)).1 t) =
    ev (((coinducedModule G M).obj.ρ (g 0)).hom (ψ (fun j ↦ g j.succ)) +
      ∑ i : Fin (r + 1), (-1 : ℤ) ^ (i.val + 1) •
        ψ (Fin.contractNth i (· * ·) g))
  simp only [map_add, map_sum, map_zsmul]
  rfl

/-- **Coinduced continuous cochains are effaceable.** Let `G` be profinite and `M` a discrete
`G`-module, `I = Map_cont(G, M)` with `(h u)(g) = u (g h)`. Then `φ(m)(g) = g m` is an injective
equivariant map `M → I` into the discrete module `I`; the homogeneous complex `K^•` of continuous
`G^{r+1} → M` (alternating omission differential) and the inhomogeneous complex `C^•(G, I)` are
isomorphic through `φ_f(g_1, …, g_r)(t) = f(t, t g_1, …, t g_1 ⋯ g_r)` with inverse
`f(x_0, …, x_r) = φ(x_0⁻¹ x_1, …, x_{r-1}⁻¹ x_r)(x_0)`; the insertion
`(H f)(x_0, …, x_{r-1}) = f(1, x_0, …, x_{r-1})` satisfies `dH + Hd = id` on `K^r`, `r ≥ 1`;
hence `H^s(C^•(G, I)) = 0` for `s ≥ 1`.

In the inhomogeneous differential the sum over `i : Fin (r + 1)` of
`(-1)^(i+1) ψ(Fin.contractNth i (· * ·) g)` contains, at `i = r`, the last face
`(-1)^(r+1) ψ(g_1, …, g_r)` (as in Mathlib's `inhomogeneousCochains.d`).

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-base-field-cd/`
`sk-lem-base-field-cd-cochains.proof.md`, Proof (1), paragraph beginning “Effaceability”.

Proof (node `lem-sfb-coinduced-cochain-contraction`):
1. Orbit embedding (uses `def-exc-continuous-cohomology`, `lem-sfb-cochain-finite-image`).
   A continuous `u : G → M` is right-invariant under an open normal `N` (finite-image
   factorization with `n = 1`); `G` acts on `I` by additive automorphisms, `N` fixes `u`, so `I`
   is discrete. For `m ∈ M` the stabilizer `U` of `m` is open and `g ↦ g m` is constant on the
   cosets `gU`, so `φ(m) ∈ I`; `φ` is additive, `φ(m)(1) = m` gives injectivity, and
   `(h φ(m))(g) = φ(m)(g h) = g h m = φ(h m)(g)` gives equivariance.
2. Coordinate isomorphism (uses `lem-sfb-cochain-finite-image`). The elements of `I` are the
   locally constant maps `G → M` (an open right stabilizer gives local constancy; conversely
   the finite-image factorization with `n = 1` gives an open normal subgroup fixing the map).
   For `f ∈ K^r` the map `(g, t) ↦ f(t, t g_1, …, t g_1 ⋯ g_r)` is locally constant on
   `G^r × G`; since `G` is compact, the open locus where it agrees with its value at `(g, t)`
   contains a product `W × G`, so `φ_f` is locally constant into `I`; conversely the
   inverse formula is locally constant. The two substitutions cancel, both maps are additive.
   With `y_0 = t`, `y_j = t g_1 ⋯ g_j`, `φ_{df}(g)(t) = Σ_i (-1)^i f(y_0, …, \hat{y_i}, …)`:
   the term `i = 0` is `(g_1 φ_f(g_2, …))(t)`, the terms `1 ≤ i ≤ r` are
   `φ_f(…, g_i g_{i+1}, …)(t)` and `i = r + 1` is `φ_f(g_1, …, g_r)(t)`; so `e ∘ d = d ∘ e`.
3. Insertion homotopy (elementary). `(dHf)(x) = Σ_i (-1)^i f(1, x_0, …, \hat{x_i}, …, x_r)` and
   `(Hdf)(x) = f(x) + Σ_i (-1)^{i+1} f(1, x_0, …, \hat{x_i}, …, x_r)`; the sums cancel, so
   `dH + Hd = id` on `K^r`, `r ≥ 1`. A cocycle `f ∈ K^s`, `s ≥ 1`, is `d(Hf)`, and the
   isomorphism of step 2 transports this vanishing to `C^•(G, I)`.

(blueprint: `lem-sfb-coinduced-cochain-contraction`) -/
theorem coinducedCochainContraction
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (M : DiscreteModule.{w} G) :
    ∃ (φ : M.obj.V →+ (coinducedModule G M).obj.V),
      Function.Injective φ ∧
      Action.IsDiscreteModule (coinducedModule G M).obj ∧
      (∀ (m : M.obj.V) (g : G), (φ m).1 g = (M.obj.ρ g).hom m) ∧
      (∀ (h : G) (m : M.obj.V),
        ((coinducedModule G M).obj.ρ h).hom (φ m) = φ ((M.obj.ρ h).hom m)) ∧
      (∀ (h : G) (m : M.obj.V) (g : G),
        (((coinducedModule G M).obj.ρ h).hom (φ m)).1 g = (φ m).1 (g * h)) ∧
      ∃ (dK : ∀ r : ℕ, coinducedHomogeneousCochains G M r →+
          coinducedHomogeneousCochains G M (r + 1))
        (dC : ∀ r : ℕ, coinducedInhomogeneousCochains G M r →+
          coinducedInhomogeneousCochains G M (r + 1))
        (e : ∀ r : ℕ, coinducedHomogeneousCochains G M r →+
          coinducedInhomogeneousCochains G M r)
        (eInv : ∀ r : ℕ, coinducedInhomogeneousCochains G M r →+
          coinducedHomogeneousCochains G M r)
        (H : ∀ r : ℕ, coinducedHomogeneousCochains G M (r + 1) →+
          coinducedHomogeneousCochains G M r),
        (∀ (r : ℕ) (f : coinducedHomogeneousCochains G M r)
          (g : Fin (r + 2) → G),
          dK r f g = ∑ i : Fin (r + 2),
            (-1 : ℤ) ^ i.val • f (coinducedOmit i g)) ∧
        (∀ (r : ℕ) (ψ : coinducedInhomogeneousCochains G M r)
          (g : Fin (r + 1) → G),
          dC r ψ g =
            ((coinducedModule G M).obj.ρ (g 0)).hom (ψ (fun j ↦ g j.succ)) +
              ∑ i : Fin (r + 1), (-1 : ℤ) ^ (i.val + 1) •
                ψ (Fin.contractNth i (· * ·) g)) ∧
        (∀ (r : ℕ) (f : coinducedHomogeneousCochains G M r)
          (g : Fin r → G) (t : G),
          (e r f g).1 t = f (fun i ↦ t * Fin.partialProd g i)) ∧
        (∀ (r : ℕ) (ψ : coinducedInhomogeneousCochains G M r)
          (x : Fin (r + 1) → G),
          eInv r ψ x = (ψ (fun i ↦ (x i.castSucc)⁻¹ * x i.succ)).1 (x 0)) ∧
        (∀ (r : ℕ) (f : coinducedHomogeneousCochains G M r),
          eInv r (e r f) = f) ∧
        (∀ (r : ℕ) (ψ : coinducedInhomogeneousCochains G M r),
          e r (eInv r ψ) = ψ) ∧
        (∀ (r : ℕ) (f : coinducedHomogeneousCochains G M r),
          e (r + 1) (dK r f) = dC r (e r f)) ∧
        (∀ (r : ℕ) (f : coinducedHomogeneousCochains G M (r + 1))
          (g : Fin (r + 1) → G),
          H r f g = f (Fin.cons 1 g)) ∧
        (∀ (r : ℕ) (f : coinducedHomogeneousCochains G M (r + 1)),
          dK r (H r f) + H (r + 1) (dK (r + 1) f) = f) ∧
        (∀ (r : ℕ) (ψ : coinducedInhomogeneousCochains G M (r + 1)),
          dC (r + 1) ψ = 0 →
            ∃ η : coinducedInhomogeneousCochains G M r,
              dC r η = ψ)
      := by
  let φ := (DiscreteModule.coind₁Lift (𝟙 M.obj.V)).hom.hom.hom
  refine ⟨φ, DiscreteModule.injective_coind₁Lift _ Function.injective_id,
    (coinducedModule G M).property, ?_, ?_, ?_, ?_⟩
  · intro m g
    rfl
  · intro h m
    exact (Action.hom_comm_apply (DiscreteModule.coind₁Lift (𝟙 M.obj.V)).hom h m).symm
  · intro h m g
    rfl
  let e := contractionCoordinates G M
  let dK := contractionDifferential G M
  let dC (r : ℕ) := (e (r + 1)).toAddMonoidHom.comp
    ((dK r).comp (e r).symm.toAddMonoidHom)
  let H := contractionInsertion G M
  refine ⟨dK, dC, (fun r ↦ (e r).toAddMonoidHom),
    (fun r ↦ (e r).symm.toAddMonoidHom), H,
    contractionDifferential_apply G M, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    contractionInsertion_identity G M, ?_⟩
  · exact contractionCoordinates_differential G M
  · intros
    rfl
  · intros
    rfl
  · intro r f
    exact (e r).symm_apply_apply f
  · intro r ψ
    exact (e r).apply_symm_apply ψ
  · intro r f
    change e (r + 1) (dK r f) = e (r + 1) (dK r ((e r).symm (e r f)))
    rw [(e r).symm_apply_apply]
  · intros
    rfl
  · intro r ψ hψ
    have hz : dK (r + 1) ((e (r + 1)).symm ψ) = 0 := by
      apply (e (r + 2)).injective
      change dC (r + 1) ψ = e (r + 2) 0
      rw [hψ, map_zero]
    have hh := contractionInsertion_identity G M r ((e (r + 1)).symm ψ)
    change dK r (H r ((e (r + 1)).symm ψ)) +
      H (r + 1) (dK (r + 1) ((e (r + 1)).symm ψ)) = (e (r + 1)).symm ψ at hh
    rw [hz, map_zero, add_zero] at hh
    refine ⟨e r (H r ((e (r + 1)).symm ψ)), ?_⟩
    change e (r + 1) (dK r ((e r).symm (e r (H r ((e (r + 1)).symm ψ))))) = ψ
    rw [(e r).symm_apply_apply, hh, (e (r + 1)).apply_symm_apply]

end
