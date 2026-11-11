/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompactObjectFiniteThickFactor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CoefficientSetup
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleRetract
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing

/-!
# The compact objects of `Loc(Dctf(X, Λ))`, finite coefficients

Let `k` be a field of finite cohomological dimension for `Λ`-modules, `X` a separated
finite-type `k`-scheme and `Λ` a finite ring whose exponent is invertible on `X`. Blueprint
`proposition-compactness-finite-coefficients--2`: the compact objects of `Loc(Dctf(X, Λ))` are
exactly the objects of `Dctf(X, Λ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.isCompactObj_iff_constructibleFiniteTor`).

The objects of `Dctf(X, Λ)` are compact
(`AlgebraicGeometry.ProEtale.DerivedCategory.isCompactObj_of_constructibleFiniteTor`).
Conversely, `Dctf(X, Λ)` compactly generates `Loc(Dctf(X, Λ))`, so a compact object is a
retract of an object of the thick closure of finitely many compact generators
(`CategoryTheory.compact_mem_finite_thick_of_generators`, Stacks Tags 09SN, 09SP, 094A); since
`Dctf(X, Λ)` is a triangulated subcategory stable under retracts
(`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor_of_retract`), this thick
closure is contained in `Dctf(X, Λ)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- `Dctf(X, Λ)` is stable under retracts, for a finite coefficient ring `Λ`. -/
lemma constructibleFiniteTor_of_retract {X : Scheme.{u}}
    {K K' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (r : Retract K K') (hK' : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K') :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K :=
  ⟨boundedConstructible_of_retract r hK'.1,
    (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_retract r hK'.2⟩

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k)))
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
  [HasInvertibleExponent Λ X]

include hk aX in
/-- The compact objects of `Loc(Dctf(X, Λ))` lie in `Dctf(X, Λ)`: the inclusion
`Loc(Dctf(X, Λ))^c ⊆ Dctf(X, Λ)` of blueprint `proposition-compactness-finite-coefficients--2`.
A compact object is a retract of an object in the thick closure of finitely many compact
generators, which are shifts of objects of `Dctf(X, Λ)`. -/
theorem constructibleFiniteTor_of_isCompactObj (C : DerivedCategoryLocalizingFiniteTor Λ X)
    (hC : BrownRepresentability.IsCompactObj C) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C.obj := by
  classical
  let L := localizingConstructibleFiniteTor Λ X
  let P' : ObjectProperty L.FullSubcategory :=
    (constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).inverseImage L.ι
  have : P'.IsTriangulated := inferInstanceAs
    ((constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).inverseImage L.ι).IsTriangulated
  have : P'.IsClosedUnderIsomorphisms := inferInstanceAs
    ((constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).inverseImage L.ι).IsClosedUnderIsomorphisms
  have : P'.IsStableUnderRetracts :=
    ⟨fun r hK' ↦ constructibleFiniteTor_of_retract (r.map L.ι) hK'⟩
  obtain ⟨ι, S, hS, hSP⟩ :=
    (compactlyGeneratesLocalizingClosure_constructibleFiniteTor Λ hk aX).1.exists_compactGenerators
  have hgen : IsTriangulatedGeneratingFamily S := by
    intro K hK
    by_contra! h
    refine hK (hS.isZero_of_forall_eq_zero K fun i f ↦ ?_)
    have h₀ := congrArg (Sigma.ι S i ≫ ·)
      (h 0 (Sigma.desc (Pi.single (M := fun j ↦ S j ⟶ K) i f) ≫
        (shiftFunctorZero _ ℤ).inv.app K))
    simpa using h₀
  obtain ⟨T, Q, hQ, ⟨r⟩⟩ := compact_mem_finite_thick_of_generators S
    (fun i ↦ (isCompactObject_iff_isCompactObj _).2 (hS.isCompactObj i)) hgen C
    ((isCompactObject_iff_isCompactObj _).2 hC)
  have hS' (i : ι) : P' (S i) := by
    obtain ⟨Y, n, hY, ⟨e⟩⟩ := hSP i
    exact P'.prop_of_iso e.symm (P'.le_shift n Y hY)
  have hsum : P' (∐ fun i : {i // i ∈ T} ↦ S i.1) :=
    P'.prop_of_iso ((biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _).symm
      (P'.prop_product fun i ↦ hS' i.1)
  exact P'.prop_of_retract r
    ((ObjectProperty.triangEnvelope_le_iff _ (Q := P')).2
      (ObjectProperty.singleton_le_iff.2 hsum) Q hQ)

include hk aX in
/-- Blueprint `proposition-compactness-finite-coefficients--2`: Compactness for finite
coefficients. For a finite ring `Λ` whose exponent is invertible on the separated finite-type
`k`-scheme `X`, over a field `k` of finite cohomological dimension for `Λ`-modules,
`Loc(Dctf(X, Λ))^c = Dctf(X, Λ)`: an object of `Loc(Dctf(X, Λ))` is compact if and only if it
lies in `Dctf(X, Λ)`. -/
theorem isCompactObj_iff_constructibleFiniteTor (C : DerivedCategoryLocalizingFiniteTor Λ X) :
    BrownRepresentability.IsCompactObj C ↔ constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C.obj :=
  ⟨constructibleFiniteTor_of_isCompactObj hk aX C, isCompactObj_of_constructibleFiniteTor hk aX C⟩

end AlgebraicGeometry.ProEtale.DerivedCategory
