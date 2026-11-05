/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusElement
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.HomotopyExactSequence
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction

/-!
# Weil groups after a finite constant field extension

Let `p : X₀ ⟶ Spec K` be a scheme over a finite field `K` with `q` elements, let `L / K` be a
finite field extension of degree `m`, and let `X₀' = X₀ ×_K Spec L`, the constant cover of `X₀`
attached to `L`, regarded as an `L`-scheme through the second projection `p'`. Base change along
the projection `π : X₀' ⟶ X₀` and a path `τ` induce an injective map
`ρ : π₁(X₀', s') → π₁(X₀, s)` (`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap`).

This file shows that `ρ` identifies the Weil group of `X₀'` over `L` with the elements of degree
divisible by `m` of the Weil group of `X₀` over `K`, the degree being divided by `m`
(blueprint `lem-wf-weil-group-constant-extension`):

* `(g, n) ∈ W(X₀', s')` if and only if `(ρ g, m n) ∈ W(X₀, s)`
  (`AlgebraicGeometry.Scheme.FiniteEtale.mem_weilGroup_constantExtension_iff`);
* if `(ρ g, n) ∈ W(X₀, s)` then `m ∣ n`
  (`AlgebraicGeometry.Scheme.FiniteEtale.dvd_of_mem_weilGroup_constantExtension`);
* if `(h, n) ∈ W(X₀, s)` and `m ∣ n`, then `h` is in the image of `ρ`
  (`AlgebraicGeometry.Scheme.FiniteEtale.mem_range_of_mem_weilGroup_constantExtension`).

The comparison of the Frobenius actions rests on the constant covers: for a finite étale
`K`-algebra `A`, the base change to `X₀'` of `X₀ ×_K Spec A` is `X₀' ×_L Spec (L ⊗_K A)`, on
whose geometric fibre the `q ^ m`-power Frobenius of `L ⊗_K A` acts as the `m`-th power of the
`q`-power Frobenius of `A`. Conversely the constant cover `X₀' ×_L Spec B` of a finite étale
`L`-algebra `B` embeds into the base change of `X₀ ×_K Spec B`. Both are instances of the map of
geometric fibres induced by a ring homomorphism `φ : A → B` over `K → L`
(`AlgebraicGeometry.Scheme.FiniteEtale.constantExtensionFiberMap`), which on the descriptions of
the fibres as sets of ring homomorphisms is precomposition with `φ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

namespace FiniteEtaleAlgebra

variable {k₀ : Type u} [Field k₀]

/-- A finite étale `k₀`-algebra `A`, as an object of `FiniteEtaleAlgebra k₀`. -/
noncomputable abbrev of (A : Type u) [CommRing A] [Algebra k₀ A] [Module.Finite k₀ A]
    [Algebra.Etale k₀ A] : FiniteEtaleAlgebra k₀ :=
  ⟨CommAlgCat.of k₀ A, inferInstanceAs (Module.Finite k₀ A), inferInstanceAs (Algebra.Etale k₀ A)⟩

variable {L : Type u} [Field L]

end FiniteEtaleAlgebra

section Frobenius

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of k₀))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀) (A : FiniteEtaleAlgebra k₀)

/-- If an integral power `Φ ^ n` of the geometric Frobenius fixes a point of the geometric fibre
of the constant cover attached to a finite field extension `L` of degree `m`, then `m ∣ n`. -/
lemma dvd_of_geometricFrobenius_zpow_apply (L : Type u) [Field L] [Algebra k₀ L]
    [Module.Finite k₀ L] [Algebra.Etale k₀ L]
    (z : (fiber s).obj (constantCover p (FiniteEtaleAlgebra.of L))) (n : ℤ)
    (h : (geometricFrobenius p s (FiniteEtaleAlgebra.of L) ^ n) z = z) :
    (Module.finrank k₀ L : ℤ) ∣ n := by
  have : Finite L := Module.finite_of_finite k₀
  have := Fintype.ofFinite k₀
  set Φ := geometricFrobenius p s (FiniteEtaleAlgebra.of L)
  have h' : (Φ⁻¹ ^ n.natAbs) z = z := by
    rcases Int.natAbs_eq n with hn | hn
    · rw [hn, zpow_natCast] at h
      rw [inv_pow]
      exact Equiv.Perm.inv_eq_iff_eq.2 h.symm
    · rw [hn, zpow_neg, zpow_natCast, ← inv_pow] at h
      exact h
  rw [Int.natCast_dvd, ← FiniteField.orderOf_frobeniusAlgHom k₀ L,
    orderOf_dvd_iff_pow_eq_one]
  refine AlgHom.ext fun x ↦ ?_
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply,
    ← Nat.card_eq_fintype_card]
  have hx : (fiberConstantCoverEquiv p s _ ((Φ⁻¹ ^ n.natAbs) z)).1 x =
      (fiberConstantCoverEquiv p s _ z).1 x := by rw [h']
  rw [fiberConstantCoverEquiv_geometricFrobenius_inv_pow] at hx
  apply (fiberConstantCoverEquiv p s _ z).1.injective
  rw [map_pow]
  exact hx

end Frobenius

variable {K : Type u} [Field K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  (L : Type u) [Field L] [Algebra K L] [Module.Finite K L] [Algebra.Etale K L]

/-- The constant field extension `X₀ ×_K Spec L` of a `K`-scheme `X₀` along a finite field
extension `L / K`: the underlying scheme of the constant cover attached to `L`. -/
noncomputable abbrev constantExtension : Scheme.{u} :=
  (constantCover p (FiniteEtaleAlgebra.of L)).obj.left

/-- The projection `π : X₀ ×_K Spec L ⟶ X₀` of the constant field extension. -/
noncomputable abbrev constantExtensionProj : constantExtension p L ⟶ X₀ :=
  (constantCover p (FiniteEtaleAlgebra.of L)).obj.hom

instance : IsFinite (constantExtensionProj p L) :=
  (constantCover p (FiniteEtaleAlgebra.of L)).property

instance : Etale (constantExtensionProj p L) :=
  (constantCover p (FiniteEtaleAlgebra.of L)).obj.prop

variable {L} {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (s' : Spec (.of Ω') ⟶ constantExtension p L)

section FiberMap

variable {A : FiniteEtaleAlgebra K} {B : FiniteEtaleAlgebra L} (φ : A.1 →+* B.1)
  (hφ : φ.comp (algebraMap K A.1) = (algebraMap L B.1).comp (algebraMap K L))

include hφ

variable [Finite K] [Finite L]

end FiberMap

section WeilGroup

variable [Finite K] [Finite L] [GeometricallyConnected p] [ConnectedSpace X₀]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ X₀}
  (τ : pullback (constantExtensionProj p L) ⋙ fiber s' ≅ fiber s)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

variable (G' : Type u) [Group G'] [∀ P, MulAction G' ((fiber s').obj P)]
  [IsNaturalSMul (fiber s') G']

end WeilGroup

section Range

variable [Finite K] [Finite L] [GeometricallyConnected p] [ConnectedSpace X₀]
  [ConnectedSpace (constantExtension p L)]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ X₀}
  (τ : pullback (constantExtensionProj p L) ⋙ fiber s' ≅ fiber s)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
  (G' : Type u) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
  [∀ P, MulAction G' ((fiber s').obj P)] [IsFundamentalGroup (fiber s') G']

end Range

section Exact

variable {K : Type u} [Field K] [Finite K] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X₀)

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [ConnectedSpace X₀] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

end Exact

end AlgebraicGeometry.Scheme.FiniteEtale
