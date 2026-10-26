/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.PointExchangeOpen
public import WeilConjectures.TraceFormula.Specialization.SupportClosureProper
public import WeilConjectures.TraceFormula.Specialization.SupportIdentityOnComponent
public import WeilConjectures.TraceFormula.Specialization.ComponentClassReduction
public import WeilConjectures.TraceFormula.Specialization.ComponentCounitIso
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF

/-!

# The compact-support exchanges of the deformation to the normal cone

For a correspondence `c` contracting at `y`, the compact-support exchanges of blueprint
`det-nearby-exchange-maps` (3) for the support map
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.supportCompactSupportExchange`, through
the compactification `C ⊂ C̄ ⟶ X ⨯ X` deformed along `c̄⁻¹(x, x)`) and for the structure map of `X`
(`ProEtale.CondensedRing.pointCompactSupportExchangeOfSeparated`, through a compactification
`X ⊂ X̄` and the dense compactification of the deformation of `X̄`) give the trace specialization
`deformationTraceSpecialization`. This file states that these exchanges specialize the class of
the component `B ∋ y` of the fixed locus
(`ProEtale.CondensedRing.Correspondence.IsContractingAt.specializesComponentClass_deformation`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence

namespace IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [Algebra k k'] (F : c.FixedLocus)

set_option maxHeartbeats 2000000 in
-- instantiating fact (III) and the reduction at the concrete data is slow
/-- **The compact-support exchanges of the deformation specialize the class of `B`** (blueprint
`det-tf-sp-theta-proper-constant`, `det-tf-sp-theta-open-constant`, with
`det-tf-fixed-deformation-points`; Varshavsky, *Lefschetz–Verdier trace formula and a
generalization of a theorem of Fujiwara*, §1.4–§2): for the exchanges `ν_c`
(`supportCompactSupportExchange`) and `ν_X` (`pointCompactSupportExchangeOfSeparated`), the
exchange `ν_F` of the fixed loci maps the specialization of the unit class of the special fixed
locus `F'` to the specialization of the class of the component `B ∋ y`. Near `y` the deformed fixed
locus is the constant family `B × S` up to nilpotents, on which `ν` is the inverse of the proper
exchange and is compatible with the specialization units. -/
theorem specializesComponentClass_deformation {B : Over (Spec (.of k))} [QuasiCompact B.hom]
    [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))}) :
    hc.SpecializesComponentClass k' (hc.supportCompactSupportExchange k')
      (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F j := by
  have hmem : (F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k)) ∈
      Set.range j.left.base := by rw [hB]; rfl
  obtain ⟨b, hbj⟩ : ∃ b : RationalPoint B, b ≫ j = F.liftPoint y hc.comp_c₁_eq_comp_c₂ := by
    have hh : Set.range (F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base ⊆
        Set.range j.left.base := by
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim (α := Spec (.of k)) p default]
    exact ⟨Over.homMk (IsOpenImmersion.lift j.left _ hh) (by
      rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]),
      Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  have hb : b ≫ j ≫ F.ι = y := by rw [← Category.assoc, hbj, FixedLocus.liftPoint_ι]
  have hI := hc.isIso_ΨF_map_componentCounit k' (hc.supportCompactSupportExchange k')
      (pointCompactSupportExchangeOfSeparated (y ≫ c.c₁) k') F j hmem
  have hbr : Set.range b.left.base = Set.univ := by
    refine Set.eq_univ_of_forall fun p ↦ ?_
    obtain ⟨q, hq⟩ : j.left.base p ∈ Set.range j.left.base := ⟨p, rfl⟩
    have h1 : j.left.base p ∈ ({(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base
        (default : Spec (.of k))} : Set _) := hB ▸ ⟨p, rfl⟩
    refine ⟨(default : Spec (.of k)), j.left.isOpenEmbedding.injective ?_⟩
    rw [Set.mem_singleton_iff] at h1
    rw [h1, ← hbj]
    rfl
  have : IsProper (deformationTotalToTrait B b.left.ker k') :=
    isProper_deformationTotalToTrait_ker B k' hbr
  have hM := (deformationModel B b.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel B _ k') (deformationModel_exists_comp_ε B _ k')
  have hN := (deformationModel c.C y.left.ker k').preservesBoundedConstructible_of_isTraitModel
    (ℓ := ℓ) (isTraitModel_deformationModel c.C _ k') (deformationModel_exists_comp_ε c.C _ k')
  have : IsProper j.left := by
    have : IsProper (j.left ≫ F.F.hom) := by rw [Over.w j]; infer_instance
    exact IsProper.of_comp _ F.F.hom
  have : IsClosedImmersion j.left := .of_isPreimmersion _ j.left.isClosedMap.isClosed_range
  have : IsClosedImmersion (j ≫ F.ι).left := by rw [Over.comp_left]; infer_instance
  have := hc.isClosedImmersion_componentSpecialLift k' j hb
  have h3 := unitClass_comp_map_comp_exchange_eq ℓ j F.ι (componentModelHom k' j hb) hM hN
    (hc.componentSpecialLift k' j hb) (hc.specialFixedLocus k').ι
    (hc.componentSpecialLift_ι k' j hb) hI
  have hD := unitClass_comp_map_comp_deformationCompactSupportExchange_app B b.left.ker k' (ℓ := ℓ)
  -- Facts (I) and (III) and the unit class identity of `ν_B` are `hI`, `h3` and `hD`; the
  -- cancellation is `TraceSpecialization.specializesComponentClass_of_eq`. Still open: fact (II),
  -- the factorization `h1` of `ν_F` on `j_! ℚ̄_ℓ`, and gluing `h3` to `hD` in `h2` (matching the
  -- statements of `h3` and of `hD` unfolds the derived categories, through the different instance
  -- paths of their unit objects).
  refine TraceSpecialization.specializesComponentClass_of_eq _ _ _ j hI
    (W := _) ?φ ((deformationCompactSupportExchange B b.left.ker k').app (𝟙_ _)) ?h1 ?h2
  all_goals sorry

end IsContractingAt

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
