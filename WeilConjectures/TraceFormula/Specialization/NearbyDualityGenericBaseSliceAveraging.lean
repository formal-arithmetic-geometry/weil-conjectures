/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs

/-!

# The slice exchange as an averaging summand

The pullback exchange `α : p^* Ψ_M ⟶ Ψ_{M''} c^*` of the projection from the generic slice model is,
at a finite level, the inclusion of the summand cut out by the averaging idempotent of a finite
group of Galois automorphisms of the slice model
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_averaging_genericSliceExchange`). This is
the generic-slicing identification `g_s^* Ψ_M ≃ (Ψ_{M''} c^*)^P` of SGA 4½, [Th. finitude], §3
(Lemme 3.4 and 3.7), with the pro-`p` averaging. It is an input owned by the nearby-cycles slice
tasks: Th. finitude 3.7 is #1790's (`trace2/nearby-finiteness-slice`), the slice traits and the
equivariance along a change of trait are `trace2/nearby-slice-traits` and
`trace2/nearby-trait-equivariance`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

namespace IsTraitModelOfGenericBase

/-- **The slice exchange is an averaging summand at a finite level** (blueprint
`det-tf-nearby-duality-slice`, the generic-slicing identification `g_s^* Ψ_M ≃ (Ψ_{M''} c^*)^P`,
with `det-tf-invariants-duality`; SGA 4½, [Th. finitude], §3). For two bounded constructible
complexes `A₁`, `A₂` on `X₁`, the pro-`p` kernel `P` of the map of inertia groups acts on
`Ψ_{M''} c^* A₁` and `Ψ_{M''} c^* A₂` through a finite quotient `Γ`: there are automorphisms
`ψ a` of the generic slice model, the identity on the total space, which act on the geometric
generic point `Spec Ω_K` through automorphisms `σ` over the generic point `η_K` of `Spec K⟦t⟧`
(the elements of `P` act through `Gal(Ω_K/η_K)`), lifting the elements `a ∈ Γ`, such that
`α_{Aᵢ}` is split by `rᵢ`
with `|Γ| • (rᵢ ≫ α_{Aᵢ}) = ∑ₐ ρ(ψ a)` and `ρ(ψ a⁻¹)` inverse to `ρ(ψ a)` on `Ψ_{M''} c^* Aᵢ`.
The order of `Γ` is invertible, the coefficients being `ℚ̄_ℓ`.

Owned by the nearby-cycles slice tasks (#1790, `trace2/nearby-slice-traits`,
`trace2/nearby-trait-equivariance`); not proved here. It is stronger than the splitting (M2)
`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom` of
#1790, which is itself `sorry` there: besides a retraction it needs the action of `P` on
`Ψ_{M''} c^* Aᵢ` to factor through a finite quotient realised by automorphisms of the slice model.
Missing are: the Galois-layer form of the slice model (an algebraic geometric generic point of the
slice trait over the strict localization `S'` of `𝔸¹_S`), Deligne's finiteness over `S'` (so that
`P` acts through a finite quotient on `ℚ̄_ℓ`-complexes), and the passage of the torsion splittings
of #1818 to `ℚ̄_ℓ` coefficients through `R lim`. -/
theorem exists_averaging_genericSliceExchange
    (A₁ A₂ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ (Γ : Type u) (_ : Group Γ) (_ : Fintype Γ)
      (ψ : Γ → (genericSliceModel (traitSliceCoord k') hb).Hom
        (genericSliceModel (traitSliceCoord k') hb) (𝟙 _) (𝟙 _)),
      (∀ a, (ψ a).total = 𝟙 _ ∧ IsIso (ψ a).generic ∧
        ∃ σ : Spec (.of (traitGenericField (traitSliceField k'))) ⟶
            Spec (.of (traitGenericField (traitSliceField k'))),
          σ ≫ traitGenericPointToSpec (traitSliceField k') =
              traitGenericPointToSpec (traitSliceField k') ∧
            (ψ a).generic ≫ pullback.snd _ _ = pullback.snd _ _ ≫ σ) ∧
      (∀ T : Dᵇc((baseChangeSpecial b (traitSlice (traitSliceCoord k'))).left)⟦
        Profinite.padicAlgClRingObj ℓ⟧, IsIso (Fintype.card Γ • 𝟙 T)) ∧
      ∀ A, (A = A₁ ∨ A = A₂) →
        ∃ r : (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).obj
            ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) ⟶
          (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj
            ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj A),
          (genericSliceExchange (traitSliceCoord k') ℓ h hb).app A ≫ r = 𝟙 _ ∧
          Fintype.card Γ • (r ≫ (genericSliceExchange (traitSliceCoord k') ℓ h hb).app A) =
            ∑ a, (genericSliceSelfAction (traitSliceCoord k') ℓ h hb (ψ a)).app _ ∧
          ∀ a, (genericSliceSelfAction (traitSliceCoord k') ℓ h hb (ψ a⁻¹)).app
              ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) ≫
            (genericSliceSelfAction (traitSliceCoord k') ℓ h hb (ψ a)).app
              ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) = 𝟙 _ := by
  sorry

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
