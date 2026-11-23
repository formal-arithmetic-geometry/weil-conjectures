/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBound
public import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleModuleObject

/-!
# The proper heart bound for the ind-constructible module objects

`AlgebraicGeometry.ProEtale.properHeartBound` and `…_padicAlgCl` bound the higher direct images
of ind-constructible sheaves along a proper morphism, with the ind-constructible sheaves taken
as the ind-closure of the constant-model constructible sheaves. On a Noetherian scheme that
ind-closure is `AlgebraicGeometry.ProEtale.IsIndConstructibleModuleObject`
(`AlgebraicGeometry.ProEtale.isIndConstructibleModuleObject_iff`), so the same three conclusions
hold for the ind-constructible module objects
(`AlgebraicGeometry.ProEtale.ProperHeartBoundModuleObjectAssertions`,
`AlgebraicGeometry.ProEtale.properHeartBound_moduleObject` and `…_padicAlgCl`): vanishing in
degrees `q > 2d + 1`, ind-constructibility in every nonnegative degree, and preservation of
arbitrary direct sums of ind-constructible sheaves by each nonnegative higher direct image.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The three conclusions of the proper heart bound, for the ind-constructible module objects
`AlgebraicGeometry.ProEtale.IsIndConstructibleModuleObject`: vanishing of the higher direct
images `R^q p_*` in degrees `q > 2d + 1`, ind-constructibility of `R^q p_* M` for `q ≥ 0`, and
preservation of arbitrary direct sums of ind-constructible sheaves by each `R^q p_*`, `q ≥ 0`. -/
def ProperHeartBoundModuleObjectAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (d : ℤ) : Prop :=
  (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    IsIndConstructibleModuleObject (condensedRingObj Λ X) M →
    (∀ q : ℤ, 2 * d + 1 < q → IsZero ((properHeartHigherDirectImage Λ p q).obj M)) ∧
    (∀ q : ℤ, 0 ≤ q → IsIndConstructibleModuleObject (condensedRingObj Λ Y)
      ((properHeartHigherDirectImage Λ p q).obj M))) ∧
  (∀ (q : ℤ), 0 ≤ q → ∀ (S : Type (u + 1))
    (M : S → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (∀ s : S, IsIndConstructibleModuleObject (condensedRingObj Λ X) (M s)) →
    ∀ c : Cofan M, IsColimit c →
      Nonempty (IsColimit ((properHeartHigherDirectImage Λ p q).mapCocone c)))

/-- On Noetherian schemes and for an `ℓ`-adic coefficient ring, the proper heart bound for the
constant-model ind-constructible sheaves gives the one for the ind-constructible module objects
(`AlgebraicGeometry.ProEtale.isIndConstructibleModuleObject_iff`). -/
theorem ProperHeartBoundAssertions.moduleObject (ℓ : ℕ) [Fact ℓ.Prime]
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : CondensedRing.IsEllAdicCoefficient ℓ Λ inferInstance)
    {X Y : Scheme.{u}} [CompactSpace X] [IsLocallyNoetherian X] [CompactSpace Y]
    [IsLocallyNoetherian Y] {p : X ⟶ Y} {d : ℤ} (h : ProperHeartBoundAssertions Λ p d) :
    ProperHeartBoundModuleObjectAssertions Λ p d := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨fun M hM ↦ ?_, fun q hq S M hM c hc ↦
    h₂ q hq S M (fun s ↦ (isIndConstructibleModuleObject_iff ℓ X Λ hΛ _).1 (hM s)) c hc⟩
  obtain ⟨hz, hind⟩ := h₁ M ((isIndConstructibleModuleObject_iff ℓ X Λ hΛ M).1 hM)
  exact ⟨hz, fun q hq ↦ (isIndConstructibleModuleObject_iff ℓ Y Λ hΛ _).2 (hind q hq)⟩

/-- **The proper heart bound for the ind-constructible module objects**, coefficient ring `E` of a
finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`: for a proper morphism `p : X ⟶ Y` of separated
finite-type schemes over a field of characteristic `p₀ ≠ ℓ` whose geometric fibres have dimension
at most `d`, the higher direct images `R^q p_*` vanish on ind-constructible sheaves for
`q > 2d + 1`, preserve ind-constructibility for `q ≥ 0`, and preserve arbitrary direct sums of
ind-constructible sheaves (`AlgebraicGeometry.ProEtale.properHeartBound`). -/
theorem properHeartBound_moduleObject
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperHeartBoundModuleObjectAssertions (Profinite.continuousMapRingObj.{u} E) p d := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  exact (properHeartBound ℓ E k p₀ hp₀ hpℓ X Y p d hd).moduleObject ℓ (.continuous _)

/-- **The proper heart bound for the ind-constructible module objects**, coefficient ring
`ℚ̄_ℓ` (`AlgebraicGeometry.ProEtale.properHeartBound_padicAlgCl`). -/
theorem properHeartBound_moduleObject_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperHeartBoundModuleObjectAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p d := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  exact (properHeartBound_padicAlgCl ℓ k p₀ hp₀ hpℓ X Y p d hd).moduleObject ℓ .algebraicClosure

end AlgebraicGeometry.ProEtale
