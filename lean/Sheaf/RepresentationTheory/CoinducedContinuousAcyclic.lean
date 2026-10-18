/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker F1
-/
module

public import Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.RepresentationTheory.CoinducedHomotopyIdentity
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Acyclicity of discrete continuous coinduction

Source: Stacks Project, Etale Cohomology, Tag 0DVG, final profinite comparison;
the coinduced contraction is an agent-written ingredient
(blueprint: lem-exc-coinduced-continuous-acyclic).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

/-- Discrete coinduced modules have zero positive continuous cochain cohomology.
The linear equivalence `eD` and `hD` specify the coinduced module of
`exists_coinduced_discrete_embedding`. Locally constant maps are exactly continuous
maps with discrete codomain. The equivalences `eK` and equation `hd` specify the
inhomogeneous complex, independently of its choice of realization. The last summand
of `hd` omits the last argument; the preceding ones multiply adjacent arguments.
For `n = 0` the same formula is the action minus the identity.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential and
final profinite comparison (blueprint: lem-exc-coinduced-continuous-acyclic).

Proof: (1) For an n-cochain F, n > 0, define
h_n(F)(g_1,...,g_{n-1})(x) = F(x,g_1,...,g_{n-1})(1).
Evaluation and precomposition are linear; `lem-exc-coinduced-homotopy-continuous`
shows that the result is continuous with values in the discrete coinduced module.
(2) Expand d h_n F and h_{n+1} d F at a tuple and then at x. Right translation
makes the surviving term (x F(g_1,...,g_n))(1) equal F(g_1,...,g_n)(x).
All other terms cancel in pairs, including the first merged and the final terms.
Thus d h_n F + h_{n+1} d F = F by `lem-exc-coinduced-homotopy-identity`.
(3) For a positive-degree cocycle d F = 0, this identity reads F = d h_n F.
Every cocycle is a coboundary, so the positive-degree homology is zero. -/
theorem coinducedContinuousCochains_isZero
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A]
    (M : DiscreteContinuousRep.{v, u, w} A G)
    (D : DiscreteContinuousRep.{v, u, max u w} A G)
    (eD : D.obj.V ≃ₗ[A] LocallyConstant G M.obj.V)
    (hD : ∀ (h : G) (f : D.obj.V) (x : G),
      eD (D.obj.ρ h f) x = eD f (x * h))
    (K : CochainComplex (ModuleCat.{max u w} A) ℕ)
    (eK : ∀ n : ℕ, K.X n ≃ₗ[A] LocallyConstant (Fin n → G) D.obj.V)
    (hd : ∀ (n : ℕ) (f : K.X n) (g : Fin (n + 1) → G),
      eK (n + 1) (K.d n (n + 1) f) g =
        D.obj.ρ (g 0) (eK n f (fun k ↦ g k.succ)) +
          ∑ k : Fin (n + 1),
            (-1 : ℤ) ^ (k.val + 1) • eK n f (Fin.contractNth k (· * ·) g)) :
    ∀ q : ℕ, 0 < q →
      IsZero ((HomologicalComplex.homologyFunctor (ModuleCat.{max u w} A)
        (ComplexShape.up ℕ) q).obj K) := by
  classical
  obtain ⟨d, h, hdformula, _, hhomotopy⟩ := coinduced_homotopy_identity G A M
  let e (n : ℕ) : K.X n ≃ₗ[A]
      LocallyConstant (Fin n → G) (LocallyConstant G M.obj.V) :=
    (eK n).trans (LocallyConstant.congrRightₗ A eD)
  have ed (n : ℕ) (f : K.X n) :
      e (n + 1) (K.d n (n + 1) f) = d n (e n f) := by
    ext g x
    rw [hdformula]
    change eD (eK (n + 1) (K.d n (n + 1) f) g) x = _
    rw [hd]
    simp only [map_add, map_sum, map_zsmul, LocallyConstant.add_apply, hD]
    congr 1
    exact (map_sum (LocallyConstant.evalₗ A x)
      (fun j : Fin (n + 1) ↦
        (-1 : ℤ) ^ (j.val + 1) • eD (eK n f (Fin.contractNth j (· * ·) g)))
      Finset.univ).trans (by rfl)
  intro q hq
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  change IsZero (K.homology (p + 1))
  apply (K.exactAt_iff_isZero_homology (p + 1)).mp
  apply (K.exactAt_iff' p (p + 1) (p + 1 + 1)
    (CochainComplex.prev_nat_succ p) (CochainComplex.next ℕ (p + 1))).mpr
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro x hx
  change K.d (p + 1) (p + 1 + 1) x = 0 at hx
  refine ⟨(e p).symm (h p (e (p + 1) x)), ?_⟩
  change K.d p (p + 1) ((e p).symm (h p (e (p + 1) x))) = x
  apply (e (p + 1)).injective
  rw [ed, LinearEquiv.apply_symm_apply]
  have hc : d (p + 1) (e (p + 1) x) = 0 := by
    rw [← ed, hx, map_zero]
  simpa only [hc, map_zero, add_zero] using hhomotopy p (e (p + 1) x)

end Rep
