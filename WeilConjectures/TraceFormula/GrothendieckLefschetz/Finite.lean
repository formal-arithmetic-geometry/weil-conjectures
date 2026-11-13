/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FrobeniusTwistFixedPoints
public import WeilConjectures.AlgebraicGeometry.GeometricFiberFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.FrobeniusCorrespondence
public import WeilConjectures.SixFunctors.Etale.Derived.FrobeniusCorrespondenceOperator
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplex

/-!
# The Grothendieck–Lefschetz trace formula with finite coefficients

Let `X₀` be a separated scheme of finite type over a finite field `k = 𝔽_q`, with geometric
fibre `X = X₀ ×_k k̄`, scheme Frobenius `Φ_X` (`Scheme.Hom.geometricFiberFrobenius`), geometric
Galois Frobenius `g_X` (`Scheme.Hom.geometricGaloisFrobenius`) over the geometric Frobenius `σ`
of `Spec k̄`, and let `Λ` be a finite ring whose exponent is invertible in `k̄`.

For `K ∈ Dᵇctf(X, Λ)` and a Frobenius correspondence `ψ : LΦ_X^* K ⟶ K`, not necessarily
invertible, the trace formula for Frobenius correspondences reads
```
tr_Λ(T_{c_m}(ψ_m) ∣ RΓ_c(X, K)) = ∑_{x̄ = Φ_X^m(x̄)} tr_Λ(ψ_{m,x̄} ∣ K_x̄)
```
for every `m ≥ 1`, the traces being categorical traces in `D(Λ)` for the Koszul braiding.

For a Weil datum `φ : Lg_X^* K ⟶ K`, the global Frobenius operator `F_{c,m} = F_c(φ^{[m]})` on
`RΓ_c(X, K)` and the local Frobenius operators `F_{x̄,m} = F_x̄(φ^{[m]})` on the stalks at the
points `x̄ ∈ X(k̄)` fixed by `(g_X^m, σ^m)`, that is at the points of `X₀(𝔽_{q^m})`
(`Etale.globalOperator`, `Etale.localOperator`), are the operators of the Frobenius
correspondence `ψ = φ ∘ κ_{1,K}`,
and the points fixed by `(g_X^m, σ^m)` are the points fixed by `Φ_X^m`. This gives
```
tr_Λ(F_{c,m} ∣ RΓ_c(X, K)) = ∑_{x̄} tr_Λ(F_{x̄,m} ∣ K_x̄).
```

## Main statements

- `AlgebraicGeometry.Etale.trace_frobeniusCompactOperator_eq_finsum`: the trace formula for
  Frobenius correspondences (stated with `sorry`).
- `AlgebraicGeometry.Etale.correspondenceOperator_iterateHom_geometricFiberFrobenius`,
  `AlgebraicGeometry.Etale.frobeniusStalkMap_iterateHom_geometricFiberFrobenius`: the operators
  of `κ_{m,K} ≫ v` are the Frobenius operators of `v` (stated with `sorry`).
- `AlgebraicGeometry.Etale.geometricFixedPointEquiv`: the points fixed by `(g_X^m, σ^m)` are the
  points fixed by `Φ_X^m`.
- `AlgebraicGeometry.Etale.finite_geometricFixedPoint`: `X₀(𝔽_{q^m})` is finite for `m ≥ 1`.
- `AlgebraicGeometry.Etale.trace_globalOperator_iterateWeilDatum_eq_finsum`: the formula for an
  arbitrary Weil datum `φ`, not necessarily invertible.
- `AlgebraicGeometry.Etale.WeilComplex.trace_globalOperator_eq_finsum`: the formula for a strict
  Weil complex.

## Implementation details

The fixed points are morphisms `x̄ : Spec k̄ ⟶ X` over `Spec k̄`; there are finitely many of
them, and the sums are `finsum`s. The perfectness of `RΓ_c(X, K)` and of the stalks is given by
right duals, as in
`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_trace_eq_globalOperatorFamily`; the
traces do not depend on their choice. The Frobenius operators use the iterates `endIterate` and
the Frobenius correspondences the iterates `ProEtale.iterateHom`; they agree
(`AlgebraicGeometry.Etale.endIterate_eq_iterateHom`,
`AlgebraicGeometry.Etale.eqToHom_comp_iterateWeilDatum`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The model Frobenius `Φ₀` of a scheme locally of finite type over `k` is finite. -/
instance [LocallyOfFiniteType f] : IsFinite f.modelFrobenius :=
  f.isFrobenius_modelFrobenius.isFinite f

/-- The scheme Frobenius `Φ_X` of the geometric fibre of a scheme locally of finite type over
`k` is finite. -/
instance [LocallyOfFiniteType f] : IsFinite f.geometricFiberFrobenius :=
  geometricFiberMap_of_isStableUnderBaseChange (P := @IsFinite) _ _ inferInstance

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Etale

open Scheme

open ProEtale (iterateHom)

section Iterate

/-- The iterate `endIterate g m` is the iterate `ProEtale.iterateHom g m`. -/
lemma endIterate_eq_iterateHom {X : Scheme.{u}} (g : X ⟶ X) (m : ℕ) :
    endIterate g m = iterateHom g m :=
  endIterate_eq_pow g m

/-- The iterates of an automorphism are its powers in `Aut X`. -/
lemma endIterate_hom_eq_pow_hom {X : Scheme.{u}} (e : Aut X) (m : ℕ) :
    endIterate e.asIso.hom m = (e ^ m).asIso.hom := by
  induction m with
  | zero => rfl
  | succ m ih => rw [endIterate_succ, ih, pow_succ, Aut.mul_asIso, Iso.trans_hom]

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The composition isomorphisms of derived pullbacks are compatible with rewriting the
morphisms along equalities. -/
lemma eqToHom_comp_leftDerivedUpperStarComp_hom_app {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    {g₂ g₂' : S ⟶ R} {g₁₂ g₁₂' : T ⟶ R} (e₂ : g₂ = g₂') (e₁₂ : g₁₂ = g₁₂')
    (h : g₁₂ = g₁ ≫ g₂) (h' : g₁₂' = g₁ ≫ g₂')
    (K : DerivedCategory (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    eqToHom (by rw [e₁₂]) ≫ (leftDerivedUpperStarComp _ g₁ g₂ g₁₂ h).hom.app K ≫
        L((g₁)^*[ModuleCat.{u + 1} Λ]).map (eqToHom (by rw [e₂])) =
      (leftDerivedUpperStarComp _ g₁ g₂' g₁₂' h').hom.app K := by
  subst e₂ e₁₂
  simp

/-- The iterates `iterateWeilDatum` (along `endIterate`) and `weilDatumIterate` (along
`ProEtale.iterateHom`) of a Weil datum agree, up to the identification
`endIterate g m = iterateHom g m`. -/
lemma eqToHom_comp_iterateWeilDatum {X : Scheme.{u}} (g : X ⟶ X)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) (m : ℕ) :
    eqToHom (by rw [endIterate_eq_iterateHom]) ≫ iterateWeilDatum Λ g φ m =
      weilDatumIterate φ m := by
  induction m with
  | zero => exact Category.id_comp _
  | succ m ih =>
    rw [iterateWeilDatum, weilDatumIterate_succ, ← ih, Functor.map_comp,
      ← eqToHom_comp_leftDerivedUpperStarComp_hom_app g (endIterate_eq_iterateHom g m).symm
        (by rw [ProEtale.iterateHom_succ, endIterate_eq_iterateHom])
        (ProEtale.iterateHom_succ g m) rfl]
    erw [Category.assoc, eqToHom_trans_assoc]
    simp

end Iterate

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The `m`-th power of the inverse `σ⁻¹` of the geometric Frobenius of `Spec k̄` is the
absolute `q ^ m`-power Frobenius of `Spec k̄`. -/
lemma specGeometricFrobenius_pow_inv_eq_iterateFrobenius (hp : (ringChar k).Prime)
    (hK : (ringChar k : Γ(Spec (.of (AlgebraicClosure k)), ⊤)) = 0) (m : ℕ) :
    (specGeometricFrobenius k ^ m).asIso.inv =
      (Spec (.of (AlgebraicClosure k))).iterateFrobenius hp hK
        (FiniteField.frobeniusExponent k * m) := by
  induction m with
  | zero =>
    rw [pow_zero, mul_zero, Scheme.iterateFrobenius_zero]
    rfl
  | succ m ih =>
    rw [pow_succ, Aut.mul_asIso, Iso.trans_inv, ih, mul_add_one, Scheme.iterateFrobenius_add,
      specGeometricFrobenius_inv_eq_iterateFrobenius k hp hK]

/-- A `k̄`-point `x̄` of the geometric fibre is fixed by the `m`-th iterate of the scheme
Frobenius `Φ_X` if and only if it is fixed by the pair `(g_X^m, σ^m)`. -/
lemma comp_iterateHom_geometricFiberFrobenius_eq_self_iff
    (x : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber) (m : ℕ) :
    x ≫ iterateHom f.geometricFiberFrobenius m = x ↔
      endIterate (specGeometricFrobenius k).asIso.hom m ≫ x =
        x ≫ endIterate f.geometricGaloisFrobenius.asIso.hom m := by
  have hp := FiniteField.ringChar_prime (k := k)
  have hK : (ringChar k : Γ(Spec (.of (AlgebraicClosure k)), ⊤)) = 0 :=
    isOfCharacteristic_Spec ringChar_cast_algebraicClosure
  have hX : (ringChar k : Γ(f.geometricFiber, ⊤)) = 0 := f.isOfCharacteristic_geometricFiber
  have H := comp_iterateFrobenius hp x hX hK
    (FiniteField.frobeniusExponent k * m)
  rw [Hom.iterateFrobenius_geometricFiber_mul_eq,
    ← specGeometricFrobenius_pow_inv_eq_iterateFrobenius hp hK] at H
  rw [endIterate_hom_eq_pow_hom, endIterate_hom_eq_pow_hom, ← Iso.eq_inv_comp, ← Category.assoc,
    ← Iso.comp_inv_eq, ← H, ← Category.assoc, eq_comm]
  exact (cancel_mono _).symm


/-- The points `x̄ ∈ X(k̄)` of the geometric fibre fixed by `(g_X^m, σ^m)`, that is
`σ^m ≫ x̄ = x̄ ≫ g_X^m`: the points of `X₀(𝔽_{q^m})`. -/
abbrev geometricFixedPoint (m : ℕ) : Type u :=
  {x : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber //
    x ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ ∧
      endIterate (specGeometricFrobenius k).asIso.hom m ≫ x =
        x ≫ endIterate f.geometricGaloisFrobenius.asIso.hom m}

/-- The points `x̄ ∈ X(k̄)` of the geometric fibre over `k̄` fixed by the `m`-th iterate of the
scheme Frobenius `Φ_X`, that is `x̄ ≫ Φ_X^m = x̄`. -/
abbrev frobeniusFixedPoint (m : ℕ) : Type u :=
  {x : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber //
    x ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ ∧
      x ≫ iterateHom f.geometricFiberFrobenius m = x}

/-- The bijection between the points fixed by `(g_X^m, σ^m)` (the points of `X₀(𝔽_{q^m})`) and
the `k̄`-points of the geometric fibre fixed by the `m`-th iterate of the scheme Frobenius
`Φ_X`; the underlying morphisms are the same. -/
def geometricFixedPointEquiv (m : ℕ) : geometricFixedPoint f m ≃ frobeniusFixedPoint f m :=
  Equiv.subtypeEquivRight fun x ↦
    and_congr_right' (comp_iterateHom_geometricFiberFrobenius_eq_self_iff f x m).symm

@[simp]
lemma coe_geometricFixedPointEquiv_apply (m : ℕ) (x : geometricFixedPoint f m) :
    (geometricFixedPointEquiv f m x).1 = x.1 :=
  rfl

@[simp]
lemma coe_geometricFixedPointEquiv_symm_apply (m : ℕ) (x : frobeniusFixedPoint f m) :
    ((geometricFixedPointEquiv f m).symm x).1 = x.1 :=
  rfl

/-- The points of `X₀(𝔽_{q^m})`, `m ≥ 1`, are finite. -/
theorem finite_geometricFixedPoint [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    {m : ℕ} (hm : m ≠ 0) : Finite (geometricFixedPoint f m) := by
  have hp := FiniteField.ringChar_prime (k := k)
  have hK : (ringChar k : Γ(Spec (.of (AlgebraicClosure k)), ⊤)) = 0 :=
    isOfCharacteristic_Spec ringChar_cast_algebraicClosure
  have := f.finite_fixedPoints_comp_absoluteFrobenius (𝟙 X₀) (Category.id_comp f) hm
    (AlgebraicClosure k) (Scheme.specAlgebraicClosure k).hom
  obtain ⟨ρ, hρ, hσ⟩ : ∃ ρ : CommRingCat.of (AlgebraicClosure k) ⟶ .of (AlgebraicClosure k),
      (∀ r, ρ.hom r = r ^ (Nat.card k ^ m)) ∧
        Spec.map ρ = (specGeometricFrobenius k ^ m).asIso.inv := by
    refine ⟨CommRingCat.ofHom (iterateFrobeniusOfPrime (AlgebraicClosure k) hp
      ringChar_cast_algebraicClosure (FiniteField.frobeniusExponent k * m)), fun r ↦ ?_, ?_⟩
    · rw [CommRingCat.hom_ofHom, iterateFrobeniusOfPrime_apply,
        FiniteField.card_eq_ringChar_pow_frobeniusExponent, ← pow_mul]
    · rw [specGeometricFrobenius_pow_inv_eq_iterateFrobenius hp hK,
        iterateFrobenius_Spec hp _ ringChar_cast_algebraicClosure]
  have hmem (x : geometricFixedPoint f m) : (x.1 ≫ f.geometricFiberProj) ≫ f =
      (Scheme.specAlgebraicClosure k).hom ∧
        (x.1 ≫ f.geometricFiberProj) ≫ 𝟙 X₀ ≫ f.absoluteFrobenius m =
          x.1 ≫ f.geometricFiberProj := by
    have hx : (specGeometricFrobenius k ^ m).asIso.hom ≫ x.1 =
        x.1 ≫ (f.geometricGaloisFrobenius ^ m).asIso.hom := by
      rw [← endIterate_hom_eq_pow_hom, ← endIterate_hom_eq_pow_hom]
      exact x.2.2
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, Hom.geometricFiber_condition]
      exact (reassoc_of% x.2.1) _
    · rw [Category.id_comp, f.isFrobenius_absoluteFrobenius m (x.1 ≫ f.geometricFiberProj) ρ hρ,
        hσ, Iso.inv_comp_eq,
        reassoc_of% hx, Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
  exact Finite.of_injective (fun x ↦ (⟨_, hmem x⟩ : {y : Spec (.of (AlgebraicClosure k)) ⟶ X₀ //
    y ≫ f = (Scheme.specAlgebraicClosure k).hom ∧ y ≫ 𝟙 X₀ ≫ f.absoluteFrobenius m = y}))
    fun x y h ↦
    Subtype.ext (Hom.geometricFiber_hom_ext f (congrArg Subtype.val h) (x.2.1.trans y.2.1.symm))

section TraceFormula

variable [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  [HasCompactification f.geometricFiberToAlgebraicClosure]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k)))]

attribute [local instance] DerivedCategory.braidedCategory'

/-- **The trace formula for Frobenius correspondences with finite coefficients**. For
`K ∈ Dᵇctf(X, Λ)`, a Frobenius correspondence `ψ : LΦ_X^* K ⟶ K` (not necessarily invertible)
and `m ≥ 1`,
```
tr_Λ(T_{c_m}(ψ_m) ∣ RΓ_c(X, K)) = ∑_{x̄ = Φ_X^m(x̄)} tr_Λ(ψ_{m,x̄} ∣ K_x̄),
```
the sum running over the `k̄`-points of `X` fixed by `Φ_X^m`. -/
theorem trace_frobeniusCompactOperator_eq_finsum
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) f.geometricFiber)
    (ψ : FrobeniusCorrespondence Λ f K) {m : ℕ} (_hm : m ≠ 0)
    [HasRightDual ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ)
      f.geometricFiberToAlgebraicClosure).obj ((DerivedCategoryFiniteTor.ι _ _).obj K))]
    [∀ x : frobeniusFixedPoint f m,
      HasRightDual ((geometricStalk Λ x.1).obj ((DerivedCategoryFiniteTor.ι _ _).obj K))] :
    trace (frobeniusCompactOperator Λ f.geometricFiberFrobenius
        f.geometricFiberFrobenius_comp_geometricFiberToAlgebraicClosure ψ m) =
      ∑ᶠ x : frobeniusFixedPoint f m,
        trace (X := (geometricStalk Λ x.1).obj ((DerivedCategoryFiniteTor.ι _ _).obj K))
          (frobeniusStalkMap x.2.2 (weilDatumIterate ψ m)) := by
  sorry

/-- For `v : L(g_X^m)^* K ⟶ K`, the operator of the Frobenius correspondence `κ_{m,K} ≫ v` along
`Φ_X^m` is the global Frobenius operator of `v`, `T(κ_{m,K} ≫ v) = F_c(v)` on `RΓ_c(X, K)`,
`κ_m : L(Φ_X^m)^* ≅ L(g_X^m)^*` being
`AlgebraicGeometry.Etale.leftDerivedUpperStarGeometricFiberFrobeniusIterateIso`. -/
theorem correspondenceOperator_iterateHom_geometricFiberFrobenius
    {K : DerivedCategory (Sheaf f.geometricFiber.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (m : ℕ)
    (v : L((endIterate f.geometricGaloisFrobenius.asIso.hom m)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K) :
    correspondenceOperator Λ (iterateHom f.geometricFiberFrobenius m)
        (ProEtale.iterateHom_comp_of_comp_eq
          f.geometricFiberFrobenius_comp_geometricFiberToAlgebraicClosure m)
        ((leftDerivedUpperStarGeometricFiberFrobeniusIterateIso _ f m).hom.app K ≫
          eqToHom (by rw [endIterate_eq_iterateHom]) ≫ v) =
      globalOperator Λ (isPullback_endIterate f.isPullback_geometricGaloisFrobenius m) v := by
  sorry

/-- At a point `x̄` fixed both by `Φ_X^m` and by `(g_X^m, σ^m)`, the stalk of the Frobenius
correspondence `κ_{m,K} ≫ v` along `Φ_X^m` is the local Frobenius operator of
`v : L(g_X^m)^* K ⟶ K`, `(κ_{m,K} ≫ v)_x̄ = F_x̄(v)` on `K_x̄`. -/
theorem frobeniusStalkMap_iterateHom_geometricFiberFrobenius
    {K : DerivedCategory (Sheaf f.geometricFiber.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (m : ℕ) {x : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber}
    (hx : endIterate (specGeometricFrobenius k).asIso.hom m ≫ x =
      x ≫ endIterate f.geometricGaloisFrobenius.asIso.hom m)
    (hx' : x ≫ iterateHom f.geometricFiberFrobenius m = x)
    (v : L((endIterate f.geometricGaloisFrobenius.asIso.hom m)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K) :
    frobeniusStalkMap hx'
        ((leftDerivedUpperStarGeometricFiberFrobeniusIterateIso _ f m).hom.app K ≫
          eqToHom (by rw [endIterate_eq_iterateHom]) ≫ v) =
      localOperator Λ hx v := by
  sorry

/-- **The trace formula for Frobenius correspondences with finite coefficients**, in terms of
the geometric Galois Frobenius `g_X`: for `K ∈ Dᵇctf(X, Λ)`, an arbitrary Weil datum
`φ : Lg_X^* K ⟶ K` and `m ≥ 1`,
`tr_Λ(F_c(φ^{[m]}) ∣ RΓ_c(X, K)) = ∑_{x̄ ∈ X₀(𝔽_{q^m})} tr_Λ(F_x̄(φ^{[m]}) ∣ K_x̄)`. -/
theorem trace_globalOperator_iterateWeilDatum_eq_finsum
    {K : DerivedCategory (Sheaf f.geometricFiber.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ f.geometricFiber K)
    (φ : (L((f.geometricGaloisFrobenius.asIso.hom)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    {m : ℕ} (hm : m ≠ 0)
    [hΓ : HasRightDual ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ)
      f.geometricFiberToAlgebraicClosure).obj K)]
    [hx : ∀ x : geometricFixedPoint f m,
      HasRightDual ((geometricStalk Λ x.1).obj K)] :
    trace (globalOperator Λ (isPullback_endIterate f.isPullback_geometricGaloisFrobenius m)
        (iterateWeilDatum Λ _ φ m)) =
      ∑ᶠ x : geometricFixedPoint f m,
        trace (localOperator Λ x.2.2 (iterateWeilDatum Λ _ φ m)) := by
  let K' : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) f.geometricFiber :=
    ObjectProperty.FullSubcategory.mk K hK
  let ψ : FrobeniusCorrespondence Λ f K' :=
    (leftDerivedUpperStarGeometricFiberFrobeniusIso _ f).hom.app K ≫ φ
  have hψ : (leftDerivedUpperStarGeometricFiberFrobeniusIterateIso _ f m).hom.app K ≫
      eqToHom (by rw [endIterate_eq_iterateHom]) ≫ iterateWeilDatum Λ _ φ m =
        weilDatumIterate ψ m := by
    rw [eqToHom_comp_iterateWeilDatum]
    exact (weilDatumIterate_comp_geometricFiberFrobenius _ f φ m).symm
  let hΓ' : HasRightDual ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ)
      f.geometricFiberToAlgebraicClosure).obj ((DerivedCategoryFiniteTor.ι _ _).obj K')) := hΓ
  let hx' (y : frobeniusFixedPoint f m) :
      HasRightDual ((geometricStalk Λ y.1).obj ((DerivedCategoryFiniteTor.ι _ _).obj K')) :=
    hx ((geometricFixedPointEquiv f m).symm y)
  rw [← correspondenceOperator_iterateHom_geometricFiberFrobenius, hψ,
    ← finsum_comp_equiv (geometricFixedPointEquiv f m).symm]
  refine (trace_frobeniusCompactOperator_eq_finsum f Λ K' ψ hm).trans (finsum_congr fun y ↦ ?_)
  have hs := frobeniusStalkMap_iterateHom_geometricFiberFrobenius f Λ m
    ((geometricFixedPointEquiv f m).symm y).2.2 y.2.2 (iterateWeilDatum Λ _ φ m)
  rw [hψ] at hs
  exact congrArg
    (trace (X := (geometricStalk Λ y.1).obj ((DerivedCategoryFiniteTor.ι _ _).obj K'))) hs

/-- **The Grothendieck–Lefschetz trace formula with finite coefficients**: for a strict Weil complex
`(K, φ)` of `Dᵇctf(X, Λ)`, `Λ` finite with exponent invertible in `k̄`, and every `m ≥ 1`,
```
tr_Λ(Frob_{X,K}^m ∣ RΓ_c(X, K)) = ∑_{y ∈ X₀(𝔽_{q^m})} tr_Λ(Frob_{y,m} ∣ K_ȳ)
```
in `End (𝟙_ D(Λ)) = Λ`. -/
theorem WeilComplex.trace_globalOperator_eq_finsum
    (W : WeilComplex (ModuleCat.{u + 1} Λ) f.geometricGaloisFrobenius.asIso) {m : ℕ} (hm : m ≠ 0)
    [HasRightDual ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ)
      f.geometricFiberToAlgebraicClosure).obj
      ((DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) f.geometricFiber).obj W.obj))]
    [∀ x : geometricFixedPoint f m,
      HasRightDual ((geometricStalk Λ x.1).obj
      ((DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) f.geometricFiber).obj W.obj))] :
    trace (globalOperator Λ (isPullback_endIterate f.isPullback_geometricGaloisFrobenius m)
        (iterateWeilDatum Λ _ W.frobenius.hom.hom m)) =
      ∑ᶠ x : geometricFixedPoint f m,
        trace (localOperator Λ x.2.2 (iterateWeilDatum Λ _ W.frobenius.hom.hom m)) :=
  trace_globalOperator_iterateWeilDatum_eq_finsum f Λ
    (K := (DerivedCategoryFiniteTor.ι _ _).obj W.obj) W.obj.property _ hm

end TraceFormula

end AlgebraicGeometry.Etale
