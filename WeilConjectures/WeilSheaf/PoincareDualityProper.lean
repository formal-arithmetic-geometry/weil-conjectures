/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Algebra.Module.ZModSelfInjective
public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.ProperUnitPairing
public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicHFinite
public import WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice

/-!
# Frobenius-equivariant Poincaré duality for a smooth proper geometrically connected scheme

Let `X₀` be smooth, proper and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, and
`Hⁱ = Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` with its geometric Frobenius `F`. For `i + j = 2d` there is a perfect
pairing `Hⁱ × Hʲ ⟶ ℚ̄_ℓ` with `⟨F x, F y⟩ = q^d ⟨x, y⟩`
(`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_cohomology_adicConstant_of_isProper`).

At each finite level `Λ = ℤ/ℓᵐ` the untwisted degreewise Poincaré pairing
`H^i_c(X̄, Λ) × H^j(X̄, Λ) ⟶ Λ(-d)` of the geometric fibre is nondegenerate
(`AlgebraicGeometry.Etale.TateOrientation.nondegenerate_untwistedDegreewisePoincarePairing`) and a
`q^d`-similitude for the Frobenius operators
(`AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_unit_frobeniusOperator`),
given the Weil equivariance of the smooth trace
(`AlgebraicGeometry.Etale.exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace`). Read through
`H^i_c = H^i` (`a` proper), the adjunction `La^* ⊣ Ra_*` (which intertwines the Frobenius operators,
`AlgebraicGeometry.Etale.frobeniusOperator_unitShiftAddEquivLowerStar`) and a trivialisation of
`Λ(-d)` over `k̄`, these are the finite-level dualities of
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_cohomology_adicConstant_of_unitPairing`, which
transports them to `ℚ̄_ℓ`
(`AlgebraicGeometry.Etale.exists_unitPairing_frobeniusOperator_geometricGaloisFrobenius`).

This is clause (1) of blueprint `thm-pod-qbar-coefficient-pairing` for the constant sheaf on a
proper `X₀` (`H_c = H`), with the similitude of `cor-pod-untwisted-similitude`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `thm-pod-qbar-coefficient-pairing` (clause (1), for the constant sheaf on a proper
`X₀`, with the similitude of `cor-pod-untwisted-similitude`): for `X₀` smooth, proper and
geometrically connected of pure dimension `d` over `k₀` and `i + j = 2d`, there is a perfect pairing
`Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ) × Hʲ(X₀ ⊗ k̄, ℚ̄_ℓ) ⟶ ℚ̄_ℓ` with `⟨F x, F y⟩ = q^d ⟨x, y⟩` for the geometric
Frobenius `F`. -/
theorem exists_isPerfPair_cohomology_adicConstant_of_isProper (i j : ℕ) (h : i + j = 2 * d) :
    ∃ P : ((adicConstant k₀ l X).cohomology i).carrier →ₗ[PadicAlgCl l]
        ((adicConstant k₀ l X).cohomology j).carrier →ₗ[PadicAlgCl l] PadicAlgCl l,
      P.IsPerfPair ∧ ∀ x y, P (((adicConstant k₀ l X).cohomology i).frobenius x)
        (((adicConstant k₀ l X).cohomology j).frobenius y) =
          (Nat.card k₀ : PadicAlgCl l) ^ d * P x y := by
  classical
  let f := X ↘ Spec (CommRingCat.of k₀)
  let a := f.geometricFiberToAlgebraicClosure
  have : ConnectedSpace f.geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := f)
      (Scheme.specAlgebraicClosure k₀).hom f.geometricFiberProj a (IsPullback.of_hasPullback _ _)
  have : IsProper a :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _) ‹_›
  have : GeometricallyConnected a :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_hasPullback _ _) ‹_›
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d a :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (IsPullback.of_hasPullback _ _) ‹_›
  have hl : ((l : ℕ) : AlgebraicClosure k₀) ≠ 0 := by
    intro h0
    have h1 : ((l : ℕ) : k₀) = 0 := by
      exact (algebraMap k₀ (AlgebraicClosure k₀)).injective (by simpa using h0)
    exact (Fact.out : ringChar k₀ ≠ l)
      ((Nat.Prime.eq_one_or_self_of_dvd (Fact.out : l.Prime) _
        (ringChar.dvd h1)).resolve_left (CharP.ringChar_ne_one))
  have hfin : ∀ m k, Finite (ProEtale.FiniteAdicH f.geometricFiber l m k) :=
    fun m k ↦ ProEtale.finite_finiteAdicH l a hl m k
  have key (m : ℕ) : ∃ P : (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
        f.geometricFiber) ⟶ (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          f.geometricFiber))⟦(i : ℤ)⟧) →+
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) f.geometricFiber) ⟶
        (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m)))
          f.geometricFiber))⟦(j : ℤ)⟧) →+ ULift.{u + 1} (ZMod (l ^ m)),
      (∀ x, (∀ y, P x y = 0) → x = 0) ∧ (∀ y, (∀ x, P x y = 0) → y = 0) ∧
      ∀ x y, P (Etale.frobeniusOperator f.geometricGaloisFrobenius.hom
          (Etale.shiftWeilDatum f.geometricGaloisFrobenius.hom
            (Etale.leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom).hom i) x)
        (Etale.frobeniusOperator f.geometricGaloisFrobenius.hom
          (Etale.shiftWeilDatum f.geometricGaloisFrobenius.hom
            (Etale.leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.hom).hom j) y) =
        (Nat.card k₀ ^ d) • P x y := by
    let Λ := ULift.{u + 1} (ZMod (l ^ m))
    have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have : NeZero (ringChar Λ) := by rw [ringChar.eq Λ (l ^ m)]; infer_instance
    have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k₀))) :=
      ⟨l ^ m, Nat.pos_of_ne_zero (NeZero.ne _), ULift.ext _ _ (by simp [Λ]), by
        simpa using ((Ne.isUnit (pow_ne_zero m hl)).map
          (Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).inv.hom)⟩
    have : HasInvertibleExponent Λ f.geometricFiber := .of_hom a
    have hcog : ∀ (M : ModuleCat.{u + 1} Λ) (x : M), x ≠ 0 → ∃ χ : M →ₗ[Λ] Λ, χ x ≠ 0 :=
      fun M x hx ↦ ZModLike.exists_apply_ne_zero (n := l ^ m)
        (Nat.pos_of_ne_zero (NeZero.ne _)) (ULift.ext _ _ (by
          simpa using (Nat.cast_pow l m).symm.trans (ZMod.natCast_self (l ^ m))))
        (fun x ↦ ⟨(ZMod.intCast_surjective x.down).choose, ULift.ext _ _ (by
          simpa using (ZMod.intCast_surjective x.down).choose_spec)⟩)
        (fun z hz ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd z _).1 (by
          simpa using congrArg ULift.down hz)) hx
    have hΛ : Function.Surjective (Int.cast : ℤ → Λ) := fun x ↦
      ⟨(ZMod.intCast_surjective x.down).choose, ULift.ext _ _
        ((ULift.down_intCast _).trans (ZMod.intCast_surjective x.down).choose_spec)⟩
    exact Etale.exists_unitPairing_frobeniusOperator_geometricGaloisFrobenius (f := f) (d := d)
      (Λ := Λ)
      hΛ hcog i j
      (by exact_mod_cast h)
  choose P hPl hPr hPF using key
  obtain ⟨P', hP', hP'F⟩ := exists_isPerfPair_cohomology_adicConstant_of_unitPairing (Y := X) hfin
    i j (Nat.card k₀ ^ d) P hPl hPr hPF
  refine ⟨P', hP', fun x y ↦ ?_⟩
  rw [hP'F, map_natCast, Nat.cast_pow]

end AlgebraicGeometry.WeilSheaf
