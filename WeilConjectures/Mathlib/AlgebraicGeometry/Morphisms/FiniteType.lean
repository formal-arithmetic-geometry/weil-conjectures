/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.RingTheory.Localization.Away.Lemmas

/-!
# Generators with a common denominator, geometrically

If `g : V ⟶ S` is locally of finite type with `V` affine, and a basic open `V_b` of `V` lies
over an affine open `W` of `S`, then the sections over `V_b` are generated as a ring by the
image of `Γ(W, ⊤)` together with finitely many quotients `t μ / b`. This is
`AlgebraicGeometry.exists_finite_subring_closure_divBasicOpen_eq_top`, the geometric form of
`Algebra.FiniteType.exists_surjective_aeval_mk'`.
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry

variable {V S : Scheme.{u}}

/-- **Generators with a common denominator, geometrically.** If `g : V ⟶ S` is locally of finite
type with `V` affine, and the basic open `V_b` lies over an affine open `W` of `S`, then there
is a finite family `t` of global sections of `V` such that `Γ(V_b, ⊤)` is generated as a ring by
the image of `Γ(W, ⊤)` together with the quotients `t μ / b`. -/
lemma exists_finite_subring_closure_divBasicOpen_eq_top (g : V ⟶ S) [IsAffine V]
    [LocallyOfFiniteType g] (b : Γ(V, ⊤)) (W : S.Opens) (hW : IsAffineOpen W)
    (hle : V.basicOpen b ≤ g ⁻¹ᵁ W) :
    ∃ (k : ℕ) (t : Fin k → Γ(V, ⊤)),
      Subring.closure (Set.range (g.resLE W (V.basicOpen b) hle).appTop ∪
        Set.range fun μ ↦ V.divBasicOpen (t μ) b) = ⊤ := by
  have : IsAffine W.toScheme := hW
  have : IsAffine (V.basicOpen b : Scheme.{u}) := (isAffineOpen_top V).basicOpen b
  have : LocallyOfFiniteType (g.resLE W (V.basicOpen b) hle) :=
    inferInstanceAs (LocallyOfFiniteType (V.homOfLE hle ≫ g ∣_ W))
  let : Algebra Γ(W.toScheme, ⊤) Γ((V.basicOpen b : Scheme.{u}), ⊤) :=
    (g.resLE W (V.basicOpen b) hle).appTop.hom.toAlgebra
  have : Algebra.FiniteType Γ(W.toScheme, ⊤) Γ((V.basicOpen b : Scheme.{u}), ⊤) :=
    HasRingHomProperty.iff_of_isAffine.mp ‹LocallyOfFiniteType (g.resLE W (V.basicOpen b) hle)›
  obtain ⟨N, k, c, hc⟩ := Algebra.FiniteType.exists_surjective_aeval_mk'
    (A := Γ(W.toScheme, ⊤)) b Γ((V.basicOpen b : Scheme.{u}), ⊤)
  -- the family is `1` together with the numerators `c ν * b`, so that `1 / b` is available
  refine ⟨k + 1, Fin.cases 1 fun ν ↦ c ν * b, (Subring.eq_top_iff' _).mpr fun x ↦ ?_⟩
  obtain ⟨p, rfl⟩ := hc x
  have hone : V.divBasicOpen 1 b ∈
      Subring.closure (Set.range ⇑(g.resLE W (V.basicOpen b) hle).appTop ∪
        Set.range fun μ : Fin (k + 1) ↦
          V.divBasicOpen (Fin.cases 1 (fun ν ↦ c ν * b) μ) b) :=
    Subring.subset_closure (Or.inr ⟨0, by simp⟩)
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine Subring.subset_closure (Or.inl ⟨a, ?_⟩)
    rw [MvPolynomial.aeval_C]
    rfl
  | add p q hp hq => simpa only [map_add] using Subring.add_mem _ hp hq
  | mul_X p μ hp =>
    rw [map_mul, MvPolynomial.aeval_X, V.mk'_eq_divBasicOpen_pow b (c μ) N]
    exact Subring.mul_mem _ hp (Subring.mul_mem _ (Subring.pow_mem _ hone N)
      (Subring.subset_closure (Or.inr ⟨μ.succ, by simp⟩)))

end AlgebraicGeometry
