/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TraceAdicConstant
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology

/-!
# The trace on `H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ)` for `X₀` smooth proper

For `X₀` smooth, proper and geometrically connected of dimension `d` over `k₀ = 𝔽_q`, the
finite-level traces `H^{2d}(X₀ ⊗ k̄, ℤ/ℓᵐ) ≅ ℤ/ℓᵐ` exist (smooth purity gives a Tate orientation
of `X₀ ⊗ k̄ ⟶ Spec k̄`), so the trace `tr : H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ` with `tr ∘ F = q^d tr`
exists as soon as the cohomology with finite coefficients is finite and the geometric Frobenius
acts on `H^{2d}(X₀ ⊗ k̄, ℤ/ℓᵐ)` by `q^d`
(`AlgebraicGeometry.WeilSheaf.exists_adicConstantTrace_of_smooth_proper`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable (k₀ l) in
/-- `ℓ^m` is invertible in a field of characteristic different from `ℓ`: the exponent of
`ℤ/ℓᵐ` is invertible on `Spec k̄`. -/
lemma hasInvertibleExponent_spec_algebraicClosure (m : ℕ) :
    HasInvertibleExponent (ULift.{u + 1} (ZMod (l ^ m)))
      (Spec (.of (AlgebraicClosure k₀))) := by
  have hp : (ringChar k₀).Prime := CharP.char_is_prime k₀ (ringChar k₀)
  have : CharP (AlgebraicClosure k₀) (ringChar k₀) :=
    charP_of_injective_algebraMap (algebraMap k₀ (AlgebraicClosure k₀)).injective _
  have hcop : Nat.Coprime (ringChar k₀) (l ^ m) :=
    ((Nat.coprime_primes hp Fact.out).2 Fact.out).pow_right m
  have hu : IsUnit ((ringChar k₀ : ℕ) : ULift.{u + 1} (ZMod (l ^ m))) := by
    have := (ZMod.unitOfCoprime _ hcop).isUnit.map ULift.ringEquiv.symm.toRingHom
    simpa using this
  have := hu.invertible
  exact HasInvertibleExponent.spec_of_charP _ (ringChar k₀)

namespace WeilSheaf

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `thm-pod-trace-isomorphism` (top degree), for `X₀` smooth proper geometrically
connected of dimension `d`: there is an isomorphism `tr : H^{2d}(X₀ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ` with
`tr ∘ F = q^d tr`, obtained from the finite-level untwisted traces
`H^{2d}(X₀ ⊗ k̄, ℤ/ℓᵐ) ≅ ℤ/ℓᵐ` of the Tate orientations given by smooth purity. The inputs are the
finiteness of `Hᵏ(X₀ ⊗ k̄, ℤ/ℓᵐ)` (`hfin`) and the action of the geometric Frobenius by `q^d` on
`H^{2d}(X₀ ⊗ k̄, ℤ/ℓᵐ)` (`hF`). -/
theorem exists_adicConstantTrace_of_smooth_proper (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    (hfin : ∀ m k, Finite (FiniteAdicH (X ↘ Spec (CommRingCat.of k₀)).geometricFiber l m k))
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
  let a := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have : IsProper a := inferInstanceAs (IsProper (Limits.pullback.snd _ _))
  have : SmoothOfRelativeDimension d a :=
    inferInstanceAs (SmoothOfRelativeDimension d (Limits.pullback.snd _ _))
  have : GeometricallyConnected a :=
    inferInstanceAs (GeometricallyConnected (Limits.pullback.snd _ _))
  have : CompactSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    QuasiCompact.compactSpace_of_compactSpace a
  have : QuasiSeparatedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    quasiSeparatedSpace_of_quasiSeparated a
  have : ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := a)
  refine exists_adicConstantTrace k₀ l X d hfin (fun m ↦ ?_) hF
  have := hasInvertibleExponent_spec_algebraicClosure k₀ l m
  have : HasInvertibleExponent (ULift.{u + 1} (ZMod (l ^ m)))
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber := HasInvertibleExponent.of_hom a
  obtain ⟨γ, -⟩ := Etale.exists_tateOrientation_traceMap_pointClass
    (Λ := ULift.{u + 1} (ZMod (l ^ m))) (d := d) a
  rw [Nat.cast_mul, Nat.cast_ofNat]
  exact Etale.TateOrientation.nonempty_addEquiv_unitShift_two_mul γ

end WeilSheaf

end AlgebraicGeometry
