/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.Algebra.Module.Lattice

/-!
# Relative length of DVR lattices and the determinant

Source: Stacks Project, Algebra, Tags 02MF, 02MG and 02MI
(`lemma-compare-lattices`, `definition-distance`, `lemma-order-vanishing-determinant`),
specialized to a DVR (blueprint: lem-exc-dvr-lattice-distance-determinant).
-/

@[expose] public section

universe u v w

namespace IsDiscreteValuationRing

private theorem length_quotient_eq_ord
    {R E : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup E] [Module R E] [Module.Free R E] [Module.Finite R E]
    (N : Submodule R E) (e : E ≃ₗ[R] N) :
    Module.length R (E ⧸ N) = Ring.ord R (LinearMap.det (N.subtype ∘ₗ e.toLinearMap)) := by
  classical
  let b := Module.Free.chooseBasis R E
  have h : Module.finrank R N = Module.finrank R E := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  let e' : E ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : E →ₗ[R] E := N.subtype ∘ₗ e'.toLinearMap
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change (b'.equiv ab (Equiv.refl _) (b' i) : E) = _
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    exact Submodule.smithNormalFormBotBasis_def b h i
  have hmat : LinearMap.toMatrix b' b' f = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Finsupp.single_eq_of_ne hij]
  have hp : Ring.ord R (∏ i, a i) = ∑ i, Ring.ord R (a i) := by
    have hn : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h
    induction (Finset.univ : Finset (Module.Free.ChooseBasisIndex R E)) using
        Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hn i)), ih]
  calc
    Module.length R (E ⧸ N) = ∑ i, Ring.ord R (a i) := by
      rw [(N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
      rfl
    _ = Ring.ord R (LinearMap.det f) := by
      rw [← LinearMap.det_toMatrix b', hmat, Matrix.det_diagonal, hp]
    _ = _ := Ring.ord_eq_of_associated
      (LinearMap.associated_det_comp_equiv N.subtype e' e)

private theorem extend_repr
    {R K V ι : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] {E : Submodule R V} [Submodule.IsLattice K E]
    [Finite ι] (b : Module.Basis ι R E) (x : E) (i : ι) :
    (b.extendOfIsLattice K).repr (x : V) i = algebraMap R K (b.repr x i) := by
  classical
  let := Fintype.ofFinite ι
  have hx : (x : V) = ∑ j, algebraMap R K (b.repr x j) •
      (b.extendOfIsLattice K) j := by
    simpa only [Module.Basis.extendOfIsLattice_apply, algebraMap_smul,
      ← Submodule.coe_smul, ← Submodule.coe_sum] using
      congrArg (fun y : E ↦ (y : V)) (b.sum_repr x).symm
  rw [hx, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

private theorem lattice_inclusion_length
    {R K V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup V]
    [Module K V] [Module R V] [IsScalarTower R K V]
    (E N : Submodule R V) [Submodule.IsLattice K E] [Submodule.IsLattice K N]
    (h : N ≤ E) (e : E ≃ₗ[R] N) :
    ∃ f : V ≃ₗ[K] V, (∀ x : E, f (x : V) = (e x : V)) ∧
      Module.length R (E ⧸ N.comap E.subtype) ≠ ⊤ ∧
      ((Module.length R (E ⧸ N.comap E.subtype)).toNat : ℤ) =
        WithZero.log (Ring.ordFrac R (LinearMap.det f.toLinearMap)) := by
  classical
  let b := Module.Free.chooseBasis R E
  let c := b.map e
  let f := (b.extendOfIsLattice K).equiv (c.extendOfIsLattice K) (Equiv.refl _)
  have hf : ∀ x : E, f (x : V) = (e x : V) := by
    have heq : f.toLinearMap.restrictScalars R ∘ₗ E.subtype = N.subtype ∘ₗ e.toLinearMap := by
      apply b.ext
      intro i
      change f ((b i : E) : V) = (e (b i) : V)
      dsimp [f]
      rw [← Module.Basis.extendOfIsLattice_apply]
      rw [Module.Basis.equiv_apply, Equiv.refl_apply]
      simp [c]
    intro x
    exact congrArg (fun l : E →ₗ[R] V ↦ l x) heq
  let e' := e.trans (Submodule.comapSubtypeEquivOfLe h).symm
  let a := (N.comap E.subtype).subtype ∘ₗ e'.toLinearMap
  have ha : ∀ x : E, (a x : V) = f (x : V) := by
    intro x
    simpa [a, e'] using (hf x).symm
  have hmat : (LinearMap.toMatrix b b a).map (algebraMap R K) =
      LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
        f.toLinearMap := by
    ext i j
    simp only [Matrix.map_apply, LinearMap.toMatrix_apply,
      Module.Basis.extendOfIsLattice_apply]
    change algebraMap R K (b.repr (a (b j)) i) =
      (b.extendOfIsLattice K).repr (f (b j)) i
    rw [← ha, extend_repr]
  have hd : algebraMap R K (LinearMap.det a) = LinearMap.det f.toLinearMap := by
    rw [← LinearMap.det_toMatrix b, RingHom.map_det]
    change ((LinearMap.toMatrix b b a).map (algebraMap R K)).det = _
    rw [hmat, LinearMap.det_toMatrix]
  have hn : LinearMap.det a ≠ 0 := by
    intro hz
    have := f.isUnit_det'.ne_zero
    exact this (by rw [← hd, hz, map_zero])
  have hl := length_quotient_eq_ord (N.comap E.subtype) e'
  have hfinite : Module.length R (E ⧸ N.comap E.subtype) ≠ ⊤ := by
    rw [hl]
    exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hn)
  refine ⟨f, hf, hfinite, ?_⟩
  rw [hl, ← hd, Ring.ordFrac_eq_ord R hn]
  rw [← Ring.ordMonoidWithZeroHom_eq_ordMonoidHom ⟨_, mem_nonZeroDivisors_of_ne_zero hn⟩]
  rfl

/-- The signed relative length of a lattice and its image is the determinant valuation.
Source: Stacks Project, Algebra, Tags 02MF, 02MG and 02MI
(blueprint: lem-exc-dvr-lattice-distance-determinant).

The submodule `(M.map (g.toLinearMap.restrictScalars R)).comap M.subtype` is the
intersection `H = M ∩ g(M)` viewed inside `M`; the other `comap` views it inside `g(M)`.
The two lengths are finite, so `ENat.toNat` followed by the cast to `ℤ` retains their values.
The normalized valuation is `WithZero.log (Ring.ordFrac R x)`: by Tag 02MD and
`Ring.ordFrac_irreducible`, it takes a uniformizer to `1` and an R-unit to `0`.

Proof (the DVR case of Tag 02MI):

1. For a finite free module `E` and a submodule `N` isomorphic to `E`, Smith normal
   form expresses `E/N` as the finite product of the cyclic quotients `R/aᵢR`.
   Their lengths are `Ring.ord R aᵢ` by definition. Length additivity and determinant
   multiplicativity show that their sum is the order of the inclusion determinant.
   Changing the isomorphism `E ≃ₗ[R] N` multiplies the determinant by a unit, preserving
   its order. This proves `length_quotient_eq_ord`, including rank zero.
2. For full lattices `N ⊆ E`, extend a basis of `E` and its image under an isomorphism
   `E ≃ₗ[R] N` to bases of `V`. Their basis equivalence `f` extends that isomorphism.
   Its matrix is the scalar extension of the inclusion matrix over `R`, since extended
   coordinates are the images of the original coordinates. Its determinant is nonzero,
   so its order is finite. The fraction-field order API identifies that finite order
   with `WithZero.log (Ring.ordFrac R (LinearMap.det f.toLinearMap))`.
3. Both `M` and `g(M)` are full lattices, and Mathlib's `Submodule.IsLattice.inf` shows
   that their intersection `H` is also a full lattice. They are finite free of the same
   rank, equal to the dimension of `V`. Choose an isomorphism `e₁ : M ≃ₗ[R] H`; the
   isomorphism `t : M ≃ₗ[R] g(M)` induced by `g` gives `e₂ = e₁ ∘ t⁻¹`.
4. Apply step 2 to `H ⊆ M` and `H ⊆ g(M)`, obtaining ambient equivalences `f₁,f₂`.
   On `M`, one has `f₁(x) = e₁(x) = e₂(g(x)) = f₂(g(x))`. Since `M` spans `V`,
   this gives `f₁ = f₂ ∘ g`. Taking determinants and their logarithmic orders gives
   `v(det f₁) = v(det f₂) + v(det g)`. Subtract the two finite length formulas.
   The two comaps in the statement are exactly `H` viewed inside the two lattices.
-/
theorem lattice_distance_determinant
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (V : Type w) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [FiniteDimensional K V] (M : Submodule R V) [Module.Finite R M]
    (hspan : Submodule.span K (M : Set V) = ⊤) (g : V ≃ₗ[K] V) :
    Module.length R
        (M ⧸ (M.map (g.toLinearMap.restrictScalars R)).comap M.subtype) ≠ ⊤ ∧
      Module.length R
        (M.map (g.toLinearMap.restrictScalars R) ⧸
          M.comap (M.map (g.toLinearMap.restrictScalars R)).subtype) ≠ ⊤ ∧
      ((Module.length R
          (M ⧸ (M.map (g.toLinearMap.restrictScalars R)).comap M.subtype)).toNat : ℤ) -
        ((Module.length R
          (M.map (g.toLinearMap.restrictScalars R) ⧸
            M.comap (M.map (g.toLinearMap.restrictScalars R)).subtype)).toNat : ℤ) =
        WithZero.log (Ring.ordFrac R (LinearMap.det g.toLinearMap)) := by
  classical
  let : Submodule.IsLattice K M :=
    ⟨Module.Finite.iff_fg.mp inferInstance, hspan⟩
  let P := M.map (g.toLinearMap.restrictScalars R)
  let t : M ≃ₗ[R] P :=
    Submodule.equivMapOfInjective (g.toLinearMap.restrictScalars R) g.injective M
  let : Submodule.IsLattice K P := by
    refine ⟨(Submodule.IsLattice.fg (M := M)).map _, ?_⟩
    change Submodule.span K (g '' (M : Set V)) = ⊤
    rw [Submodule.span_image_linearEquiv, hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr g.surjective
  let H := M ⊓ P
  have hr : Module.finrank R M = Module.finrank R H := by
    have hrank := (Submodule.IsLattice.rank' K M).trans
      (Submodule.IsLattice.rank' K H).symm
    simpa only [← Module.finrank_eq_rank, Nat.cast_inj] using hrank
  let e : M ≃ₗ[R] H := LinearEquiv.ofFinrankEq M H hr
  let e' : P ≃ₗ[R] H := t.symm.trans e
  obtain ⟨f₁, hf₁, hlen₁, hval₁⟩ :=
    lattice_inclusion_length M H inf_le_left e
  obtain ⟨f₂, hf₂, hlen₂, hval₂⟩ :=
    lattice_inclusion_length P H inf_le_right e'
  have hcomp : f₁.toLinearMap = f₂.toLinearMap ∘ₗ g.toLinearMap := by
    apply (Module.Free.chooseBasis R M |>.extendOfIsLattice K).ext
    intro i
    simp only [Module.Basis.extendOfIsLattice_apply, LinearMap.comp_apply]
    change f₁ ((Module.Free.chooseBasis R M i : M) : V) =
      f₂ (g ((Module.Free.chooseBasis R M i : M) : V))
    rw [hf₁]
    change _ = f₂ (t (Module.Free.chooseBasis R M i) : V)
    rw [hf₂]
    simp [e']
  have hd := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp] at hd
  have hn₂ : LinearMap.det f₂.toLinearMap ≠ 0 :=
    f₂.isUnit_det'.ne_zero
  have hng : LinearMap.det g.toLinearMap ≠ 0 :=
    g.isUnit_det'.ne_zero
  have hv := congrArg (fun x ↦ WithZero.log (Ring.ordFrac R x)) hd
  rw [map_mul, WithZero.log_mul ((map_ne_zero (Ring.ordFrac (K := K) R)).mpr hn₂)
    ((map_ne_zero (Ring.ordFrac (K := K) R)).mpr hng)] at hv
  have hH₁ : H.comap M.subtype = P.comap M.subtype := by
    ext x
    simp [H]
  have hH₂ : H.comap P.subtype = M.comap P.subtype := by
    ext x
    simp [H]
  rw [hH₁] at hlen₁ hval₁
  rw [hH₂] at hlen₂ hval₂
  refine ⟨hlen₁, hlen₂, ?_⟩
  rw [hval₁, hval₂]
  omega

end IsDiscreteValuationRing
