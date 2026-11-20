/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleFilteredColimits
public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleExtensions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible

/-!
# Ind-constructible sheaves as ind-objects of the constructible module objects

On a Noetherian scheme `X` and for an `ℓ`-adic coefficient ring `Λ`
(`AlgebraicGeometry.ProEtale.CondensedRing.IsEllAdicCoefficient`), the constant-model
constructibility predicate `IsConstantModelConstructible Λ X` is the constructibility predicate
of module objects `IsConstructibleModuleObject (condensedRingObj Λ X)`
(`AlgebraicGeometry.ProEtale.adicConstructibilityPredicateComparison`). Hence the ind-closure of
the constructible sheaves, `AlgebraicGeometry.ProEtale.IsIndConstructibleModuleObject`, agrees
with the ind-closure of the constant-model constructible sheaves, and the closure properties of
the latter transport: closure under extensions
(`AlgebraicGeometry.ProEtale.isIndConstructibleModuleObject_of_shortExact`,
`…_of_shortExact_padicAlgCl`) and under filtered colimits and arbitrary direct sums
(`AlgebraicGeometry.ProEtale.isIndConstructibleModuleObject_filteredColimits_and_sums`,
`…_filteredColimits_and_sums_padicAlgCl`), for the coefficient rings `E` (a finite extension
of `ℚ_ℓ` inside `ℚ̄_ℓ`) and `ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- On a Noetherian scheme, the constant-model constructibility predicate of an `ℓ`-adic
coefficient ring is the constructibility predicate of module objects
(`AlgebraicGeometry.ProEtale.adicConstructibilityPredicateComparison`, as an equality of
object properties). -/
theorem isConstantModelConstructible_eq_isConstructibleModuleObject (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : CondensedRing.IsEllAdicCoefficient ℓ Λ inferInstance) :
    IsConstantModelConstructible Λ X = IsConstructibleModuleObject (condensedRingObj Λ X) :=
  funext fun M ↦ propext ((adicConstructibilityPredicateComparison ℓ X Λ hΛ).1 M).symm

/-- On a Noetherian scheme and for an `ℓ`-adic coefficient ring, a sheaf of modules is
ind-constructible if and only if it is an ind-object of the constant-model constructible
sheaves. -/
theorem isIndConstructibleModuleObject_iff (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : CondensedRing.IsEllAdicCoefficient ℓ Λ inferInstance)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIndConstructibleModuleObject (condensedRingObj Λ X) M ↔
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) M := by
  rw [isConstantModelConstructible_eq_isConstructibleModuleObject ℓ X Λ hΛ]

/-- **Extensions of ind-constructible sheaves are ind-constructible**, for the coefficient ring
`E` of a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`: the constant-model statement
`AlgebraicGeometry.ProEtale.indConstructible_of_shortExact` transported along
`AlgebraicGeometry.ProEtale.isIndConstructibleModuleObject_iff`. -/
theorem isIndConstructibleModuleObject_of_shortExact
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hS : S.ShortExact)
    (hN : IsIndConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj E) X)
      S.X₁)
    (hB : IsIndConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj E) X)
      S.X₃) :
    IsIndConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj E) X)
      S.X₂ := by
  have hΛ : CondensedRing.IsEllAdicCoefficient ℓ (Profinite.continuousMapRingObj E)
      inferInstance := .continuous _
  rw [isIndConstructibleModuleObject_iff ℓ X _ hΛ] at hN hB ⊢
  exact indConstructible_of_shortExact ℓ E X S hS hN hB

/-- **Extensions of ind-constructible sheaves are ind-constructible**, for the coefficient ring
`ℚ̄_ℓ`: the constant-model statement
`AlgebraicGeometry.ProEtale.indConstructible_of_shortExact_padicAlgCl` transported along
`AlgebraicGeometry.ProEtale.isIndConstructibleModuleObject_iff`. -/
theorem isIndConstructibleModuleObject_of_shortExact_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hS : S.ShortExact)
    (hN : IsIndConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      S.X₁)
    (hB : IsIndConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      S.X₃) :
    IsIndConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      S.X₂ := by
  have hΛ : CondensedRing.IsEllAdicCoefficient ℓ (Profinite.padicAlgClRingObj ℓ)
      inferInstance := .algebraicClosure
  rw [isIndConstructibleModuleObject_iff ℓ X _ hΛ] at hN hB ⊢
  exact indConstructible_of_shortExact_padicAlgCl ℓ X S hS hN hB

/-- **Ind-constructible sheaves are closed under filtered colimits and direct sums**, for the
coefficient ring `E` of a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` and a separated finite-type
scheme over a field of characteristic `p ≠ ℓ`: the constant-model statement
`AlgebraicGeometry.ProEtale.indConstructible_filteredColimits_and_sums` transported along
`AlgebraicGeometry.ProEtale.isIndConstructibleModuleObject_iff`. -/
theorem isIndConstructibleModuleObject_filteredColimits_and_sums
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (B : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
      (c : Cocone B), IsColimit c →
      (∀ i : I, IsIndConstructibleModuleObject
        (condensedRingObj (Profinite.continuousMapRingObj E) X) (B.obj i)) →
      IsIndConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj E) X)
        c.pt) ∧
    (∀ (S : Type (u + 1))
      (B : S → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
      (c : Cofan B), IsColimit c →
      (∀ s : S, IsIndConstructibleModuleObject
        (condensedRingObj (Profinite.continuousMapRingObj E) X) (B s)) →
      IsIndConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj E) X)
        c.pt) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have hΛ : CondensedRing.IsEllAdicCoefficient ℓ (Profinite.continuousMapRingObj E)
      inferInstance := .continuous _
  obtain ⟨h₁, h₂⟩ := indConstructible_filteredColimits_and_sums ℓ E k p hp hpl X
  refine ⟨fun I _ _ B c hc hB ↦ ?_, fun S B c hc hB ↦ ?_⟩
  · rw [isIndConstructibleModuleObject_iff ℓ X _ hΛ]
    exact h₁ I B c hc fun i ↦ (isIndConstructibleModuleObject_iff ℓ X _ hΛ _).1 (hB i)
  · rw [isIndConstructibleModuleObject_iff ℓ X _ hΛ]
    exact h₂ S B c hc fun s ↦ (isIndConstructibleModuleObject_iff ℓ X _ hΛ _).1 (hB s)

/-- **Ind-constructible sheaves are closed under filtered colimits and direct sums**, for the
coefficient ring `ℚ̄_ℓ` and a separated finite-type scheme over a field of characteristic
`p ≠ ℓ`: the constant-model statement
`AlgebraicGeometry.ProEtale.indConstructible_filteredColimits_and_sums_padicAlgCl` transported
along `AlgebraicGeometry.ProEtale.isIndConstructibleModuleObject_iff`. -/
theorem isIndConstructibleModuleObject_filteredColimits_and_sums_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (B : I ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (c : Cocone B), IsColimit c →
      (∀ i : I, IsIndConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) (B.obj i)) →
      IsIndConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
        c.pt) ∧
    (∀ (S : Type (u + 1))
      (B : S → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (c : Cofan B), IsColimit c →
      (∀ s : S, IsIndConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) (B s)) →
      IsIndConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
        c.pt) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have hΛ : CondensedRing.IsEllAdicCoefficient ℓ (Profinite.padicAlgClRingObj ℓ)
      inferInstance := .algebraicClosure
  obtain ⟨h₁, h₂⟩ := indConstructible_filteredColimits_and_sums_padicAlgCl ℓ k p hp hpl X
  refine ⟨fun I _ _ B c hc hB ↦ ?_, fun S B c hc hB ↦ ?_⟩
  · rw [isIndConstructibleModuleObject_iff ℓ X _ hΛ]
    exact h₁ I B c hc fun i ↦ (isIndConstructibleModuleObject_iff ℓ X _ hΛ _).1 (hB i)
  · rw [isIndConstructibleModuleObject_iff ℓ X _ hΛ]
    exact h₂ S B c hc fun s ↦ (isIndConstructibleModuleObject_iff ℓ X _ hΛ _).1 (hB s)

end AlgebraicGeometry.ProEtale
