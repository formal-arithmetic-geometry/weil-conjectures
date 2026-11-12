/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentSpecializationIntegral
public import WeilConjectures.TraceFormula.Specialization.DeformationExchange
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorShift
public import WeilConjectures.TraceFormula.Specialization.TraitSpecializationFaithful

/-!
# Specialization when the fixed point scheme is a constant family

Let `c` be contracting at the `k`-point `y` and let `B ∋ y` be an open and closed subscheme of the
fixed locus, proper over `k`, with underlying set `{y}`, so that near `y` the deformed fixed locus
is the constant family `B × S` up to nilpotents. For the trace specialization of the deformation
to the normal cone (`Correspondence.IsContractingAt.deformationTraceSpecialization`, with the
exchanges `supportCompactSupportExchange` and `pointCompactSupportExchangeOfSeparated`), this file
states the two clauses of blueprint `corollary-specialization-when-fixed-point-scheme`:

* `sp_F` is the identity under the identifications of Borel–Moore sections of `B` and of the
  special fixed locus with `End(ℚ̄_ℓ)` given by integration
  (`Correspondence.IsContractingAt.integral_sp_deformationTraceSpecialization`);
* in particular `sp_F` is injective on sections over `B`
  (`Correspondence.IsContractingAt.restrict_eq_of_sp_deformationTraceSpecialization_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The nearby cycles `Ψ_s` of the trait `S = Spec k'⟦t⟧` are injective on the endomorphisms of
the unit of `Dᵇc(Spec k)⟦ℚ̲̄_ℓ⟧`. -/
theorem traitSpecialization_map_injective (k : Type u) [Field k] (k' : Type u) [Field k']
    [Algebra k k'] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime]
    [Fact (ringChar k' ≠ ℓ)] :
    Function.Injective (fun f : 𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶ 𝟙_ _ ↦
      (traitSpecialization k k' (ℓ := ℓ)).map f) := by
  have : (traitSpecialization k k' (ℓ := ℓ)).Additive := by
    unfold traitSpecialization NearbyCyclesModel.boundedConstructibleNearbyCycles
    infer_instance
  intro f g h
  rw [← sub_eq_zero, ← traitSpecialization_map_eq_zero_iff k k', Functor.map_sub]
  exact sub_eq_zero.mpr h

namespace Correspondence.IsContractingAt

attribute [local instance] isIso_traitSpecializationUnit

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k'] (F : c.FixedLocus)
  {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
  [IsOpenImmersion j.left]

/-- **Specialization when the fixed point scheme is a constant family** (blueprint
`corollary-specialization-when-fixed-point-scheme--1`, the case `F_red = {y} × S`): for the trace
specialization of the deformation to the normal cone of a contracting point `y` and a component
`B ∋ y` of the fixed locus, open, closed, proper and with underlying set `{y}`, the specialization
`sp_F` is the identity under the identifications of Borel–Moore sections of `B` and of the special
fixed locus with `End(ℚ̄_ℓ)` given by integration and the specialization `Ψ_s` of the base point,
conjugated by its unit `σ_s`: `∫ sp_F(z) = σ_s⁻¹ ∘ Ψ_s(∫_B z|_B) ∘ σ_s`. -/
theorem integral_sp_deformationTraceSpecialization
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))})
    (z : BorelMooreSection ℓ F.F) :
    ((hc.deformationTraceSpecialization k' (hc.supportCompactSupportExchange k')
        (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F).sp z).integral =
      traitSpecializationUnit k k' ≫ (traitSpecialization k k').map (z.restrict j).integral ≫
        inv (traitSpecializationUnit k k') :=
  hc.integral_sp_eq_map_integral_restrict k' j
    (hc.specializesComponentClass_deformation k' F j hB) z

/-- **The specialization is injective on a constant component** (blueprint
`corollary-specialization-when-fixed-point-scheme--2`): for the trace specialization of the
deformation to the normal cone of a contracting point `y` and a component `B ∋ y` of the fixed
locus, open, closed, proper and with underlying set `{y}`, two Borel–Moore sections of the fixed
locus with the same specialization have the same restriction to `B`. It follows from
`integral_sp_deformationTraceSpecialization`, the injectivity of `Ψ_s` on `End(ℚ̄_ℓ)`
(`traitSpecialization_map_injective`) and of integration over the thickened point `B`
(`BorelMooreSection.integral_injective`). -/
theorem restrict_eq_of_sp_deformationTraceSpecialization_eq
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))})
    {z₁ z₂ : BorelMooreSection ℓ F.F}
    (h : (hc.deformationTraceSpecialization k' (hc.supportCompactSupportExchange k')
        (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F).sp z₁ =
      (hc.deformationTraceSpecialization k' (hc.supportCompactSupportExchange k')
        (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F).sp z₂) :
    z₁.restrict j = z₂.restrict j := by
  have h₂ := congrArg BorelMooreSection.integral h
  rw [hc.integral_sp_deformationTraceSpecialization k' F j hB,
    hc.integral_sp_deformationTraceSpecialization k' F j hB, cancel_epi, cancel_mono] at h₂
  obtain ⟨b, -, hb⟩ := RationalPoint.exists_lift_of_range_eq_singleton j _ hB
  exact BorelMooreSection.integral_injective b hb (traitSpecialization_map_injective k k' h₂)

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
