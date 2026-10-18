/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.TopDegree
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicDuality
public import WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice
public import WeilConjectures.WeilSheaf.TraceIsomorphism

/-!
# The trace on the top cohomology of the constant Weil sheaf

Let `X₀` be proper and geometrically connected over `k₀ = 𝔽_q`, with geometric fiber
`X = X₀ ⊗ k̄` of relative dimension `d`. The trace `tr : H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ`
(`AlgebraicGeometry.WeilSheaf.exists_adicConstantTrace`) is obtained from the finite-level
untwisted traces `tr^{(-d)} : H^{2d}(X, ℤ/ℓᵐ) ≅ Λ(-d) ≅ ℤ/ℓᵐ`
(`AlgebraicGeometry.Etale.TateOrientation.nonempty_addEquiv_unitShift_two_mul`): they define
nondegenerate pairings `H^{2d}(X, ℤ/ℓᵐ) × H^0(X, ℤ/ℓᵐ) ⟶ ℤ/ℓᵐ`, `⟨x, y⟩ = tr(x) · y`, which the
`ℓ`-adic transport
(`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_cohomology_adicConstant_of_unitPairing`)
carries to a perfect pairing `H^{2d} × H^0 ⟶ ℚ̄_ℓ`; the trace is the pairing with the unit
`1 ∈ H^0 = ℚ̄_ℓ`, on which Frobenius acts trivially. No compatibility of the finite-level traces
in `m` is needed: the transport extracts a compatible family by compactness.

Frobenius acts on `ℚ̄_ℓ(-d)` by `q^d`: this is the input `hF` that the geometric Frobenius acts on
`H^{2d}(X, ℤ/ℓᵐ)` by `q^d`, which is the trace square of
`thm-pur-weil-equivariance-of-purity-and-trace` read through the bijective untwisted trace.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

set_option maxHeartbeats 1600000 in
-- the indices `((0 : ℕ) : ℤ)` and `0` of the cohomology groups are only definitionally equal
/-- Blueprint `thm-pod-trace-isomorphism` (top degree, constant coefficients), for `X₀` proper:
the trace `tr : H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ` on which Frobenius acts by `q^d`. It is obtained by
transport from the finite-level untwisted traces `H^{2d}(X, ℤ/ℓᵐ) ≅ ℤ/ℓᵐ` (`htr`), given that the
cohomology `Hᵏ(X, ℤ/ℓᵐ)` is finite (`hfin`) and that the geometric Frobenius acts on
`H^{2d}(X, ℤ/ℓᵐ)` by `q^d` (`hF`). -/
theorem exists_adicConstantTrace (d : ℕ)
    [CompactSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [QuasiSeparatedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]
    (hfin : ∀ m k, Finite (FiniteAdicH (X ↘ Spec (CommRingCat.of k₀)).geometricFiber l m k))
    (htr : ∀ m : ℕ, Nonempty
      ((𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))⟦((2 * d : ℕ) : ℤ)⟧) ≃+
        ULift.{u + 1} (ZMod (l ^ m))))
    (hF : ∀ (m : ℕ) (x : 𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))⟦((2 * d : ℕ) : ℤ)⟧),
      Etale.frobeniusOperator (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
        (Etale.shiftWeilDatum (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
          (Etale.leftDerivedUpperStarUnitIso _
            (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).hom ((2 * d : ℕ) : ℤ))
        x = (Nat.card k₀ ^ d) • x) :
    ∃ tr : ((adicConstant k₀ l X).cohomology ((2 * d : ℕ) : ℤ)).carrier ≃ₗ[PadicAlgCl l]
        PadicAlgCl l,
      ∀ z, tr (((adicConstant k₀ l X).cohomology ((2 * d : ℕ) : ℤ)).frobenius z) =
        (Nat.card k₀ : PadicAlgCl l) ^ d * tr z := by
  let Λ (m : ℕ) := ULift.{u + 1} (ZMod (l ^ m))
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let t (m : ℕ) := (htr m).some
  let μ (m : ℕ) : (𝟙_ (Etale.DerivedCategoryModule (Λ m) Y) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (Λ m) Y))⟦((0 : ℕ) : ℤ)⟧) ≃+ Λ m :=
    (Etale.nonempty_addEquiv_unitShift_zero (Λ m) Y).some
  let P (m : ℕ) : (𝟙_ (Etale.DerivedCategoryModule (Λ m) Y) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (Λ m) Y))⟦((2 * d : ℕ) : ℤ)⟧) →+
      (𝟙_ (Etale.DerivedCategoryModule (Λ m) Y) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (Λ m) Y))⟦((0 : ℕ) : ℤ)⟧) →+ Λ m :=
    AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ t m x * μ m y)
      fun y y' ↦ by rw [map_add, mul_add]) fun x x' ↦ by
        refine AddMonoidHom.ext fun y ↦ ?_
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_mul]
  have hP (m : ℕ) x y : P m x y = t m x * μ m y := rfl
  have hPl (m : ℕ) x (hx : ∀ y, P m x y = 0) : x = 0 := by
    have h := hx ((μ m).symm 1)
    rw [hP, AddEquiv.apply_symm_apply, mul_one] at h
    exact (t m).injective (h.trans (map_zero _).symm)
  have hPr (m : ℕ) y (hy : ∀ x, P m x y = 0) : y = 0 := by
    have h := hy ((t m).symm 1)
    rw [hP, AddEquiv.apply_symm_apply, one_mul] at h
    exact (μ m).injective (h.trans (map_zero _).symm)
  obtain ⟨P', hP', hP'F⟩ := exists_isPerfPair_cohomology_adicConstant_of_unitPairing
    (k₀ := k₀) (l := l) (Y := X) hfin (2 * d) 0 (Nat.card k₀ ^ d) P hPl hPr (by
      intro m x y
      rw [hP, hP, hF]
      erw [Etale.frobeniusOperator_shiftWeilDatum_zero]
      rw [map_nsmul, smul_mul_assoc])
  obtain ⟨e, he⟩ := exists_linearEquiv_cohomology_zero_adicConstant k₀ l X
  let u := e.symm 1
  have hu : ((adicConstant k₀ l X).cohomology ((0 : ℕ) : ℤ)).frobenius u = u :=
    e.injective (he u)
  have hspan (v : ((adicConstant k₀ l X).cohomology ((0 : ℕ) : ℤ)).carrier) : v = e v • u := by
    apply e.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hu0 : u ≠ 0 := fun h ↦ (one_ne_zero (α := PadicAlgCl l)) (by simpa [u] using congrArg e h)
  have hinj : Function.Injective (P'.flip u) := by
    refine (injective_iff_map_eq_zero _).2 fun z hz ↦ hP'.bijective_left.1 ?_
    rw [map_zero]
    refine LinearMap.ext fun v ↦ ?_
    rw [hspan v, map_smul, LinearMap.zero_apply]
    simp only [LinearMap.flip_apply] at hz
    rw [hz, smul_zero]
  have hsurj : Function.Surjective (P'.flip u) := by
    have hne : P'.flip u ≠ 0 := fun h ↦ hu0 (hP'.bijective_right.1 (h.trans (map_zero _).symm))
    obtain ⟨z, hz⟩ : ∃ z, P'.flip u z ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (LinearMap.ext hcon)
    intro c
    refine ⟨(c / P'.flip u z) • z, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hz]
  refine ⟨LinearEquiv.ofBijective (P'.flip u) ⟨hinj, hsurj⟩, fun z ↦ ?_⟩
  simp only [LinearEquiv.ofBijective_apply, LinearMap.flip_apply]
  conv_lhs => rw [← hu]
  rw [hP'F, map_natCast, Nat.cast_pow]

end WeilSheaf

end AlgebraicGeometry
