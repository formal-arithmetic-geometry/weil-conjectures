/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import WeilConjectures.AlgebraicGeometry.Curve.CoefficientPair
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenVanishingComparison
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison

/-!
# The eight curve assertions on a dense open

Source: Stacks Project, Etale Cohomology, Lemma 0GJA, Situation 0A52.

The unconditional equivalence, without a condition on the torsion of the sheaf, is
`AlgebraicGeometry.IsCurve.assertions_iff_dense_open`, a corollary of the curve package.

## Implementation details

Abelian sheaves are converted to sheaves of `ULift ℤ`-modules by the same coefficient functor as
in `IsCurve.finite_pushforward_assertions`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Let `F` be a constructible torsion sheaf on a curve over an algebraically closed field and
`U` a dense open. If the eight assertions hold for the extension by zero of `F|_U`, they hold for
`F`. The converse holds when `F` has torsion prime to the characteristic or is `p`-primary for
`p = char k`, and hence when `F` is killed by a prime.
Source: Stacks Project, Lemma 0GJA and Situation 0A52. -/
theorem IsCurve.dense_open_assertions {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    (IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G →
      IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F →
        IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G) ∧
    (∀ r : ℕ, r.Prime → r • 𝟙 P.F = 0 →
      (IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F ↔
        IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G)) :=
  by
    dsimp only
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let T := sheafCompose P.C.smallEtaleTopology E
    let F := T.obj P.F
    let G := T.obj ((Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F))
    obtain ⟨hhigh, hprimary₁, hprimary₂⟩ :=
      IsCurve.dense_open_vanishing_comparison P U hU
    obtain ⟨hfinite₁, hfinite₂, hproperFinite₁, hproperFinite₂⟩ :=
      IsCurve.dense_open_finiteness_comparison P hP U hU
    obtain ⟨hbase₁, hbase₂, hproperBase₁, hproperBase₂⟩ :=
      IsCurve.dense_open_baseChange_comparison P U hU
    have hrestrict := IsCurve.dense_open_restriction_comparison P U hU
    have hforward : IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G →
        IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F :=
      fun h ↦ (IsCurve.assertions_iff _ _ _).mpr
      ⟨(fun q hq ↦ ((hhigh q (by omega)).some.toEquiv.subsingleton_congr).mp
          (h.subsingleton_of_two_lt q hq)),
       (fun q hq ↦ ((hhigh q hq).some.toEquiv.subsingleton_congr).mp
          (h.subsingleton_of_one_lt_of_isAffine q hq)),
       hprimary₁ h.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf,
       hfinite₁ (@h.finite_of_isTorsionSheafOfInvertibleOrder),
       hproperFinite₁ (@h.finite_of_isProper),
       hbase₁ (@h.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder),
       hproperBase₁ (@h.bijective_cohomologyMap_of_isProper),
       hrestrict.mpr h.surjective_cohomologyMap_of_isOpenImmersion⟩
    have hreverse :
        (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
          ∃ p : ℕ, p.Prime ∧ CharP k p ∧
            Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
        IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F →
        IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G :=
      fun ht h ↦ (IsCurve.assertions_iff _ _ _).mpr
      ⟨(fun q hq ↦ ((hhigh q (by omega)).some.toEquiv.subsingleton_congr).mpr
          (h.subsingleton_of_two_lt q hq)),
       (fun q hq ↦ ((hhigh q hq).some.toEquiv.subsingleton_congr).mpr
          (h.subsingleton_of_one_lt_of_isAffine q hq)),
       hprimary₂ ht h.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf,
       hfinite₂ ht (@h.finite_of_isTorsionSheafOfInvertibleOrder),
       hproperFinite₂ ht (@h.finite_of_isProper),
       hbase₂ ht (@h.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder),
       hproperBase₂ ht (@h.bijective_cohomologyMap_of_isProper),
       hrestrict.mp h.surjective_cohomologyMap_of_isOpenImmersion⟩
    refine ⟨hforward, hreverse, ?_⟩
    intro r hr hkill
    have : (forget₂ (ModuleCat.{u + 1} ℤ)
        AddCommGrpCat.{u + 1}).asEquivalence.functor.Additive := by
      change (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).Additive
      infer_instance
    have : (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv.Additive :=
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.inverse_additive
    have : E.Additive := inferInstance
    have : T.Additive := by
      dsimp [T, sheafCompose]
      infer_instance
    have hkillF : r • 𝟙 (T.obj P.F) = 0 := by
      have hh := congrArg T.map hkill
      rw [T.map_nsmul, T.map_id, T.map_zero] at hh
      exact hh
    have hstalk (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (.of Ω) ⟶ P.C)
        (x : ↥((Scheme.pointSmallEtale s).sheafFiber.obj (T.obj P.F))) : r • x = 0 := by
      let S := (Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      have : Limits.HasLimitsOfSize.{u, u}
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      have : Limits.HasFiniteLimits
          (Sheaf P.C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :=
        inferInstance
      have : S.Additive := by
        exact @GrothendieckTopology.Point.sheafFiber_additive.{u, u + 1, u + 2, u, u + 1}
          _ _ _ (Scheme.pointSmallEtale s) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          (ModuleCat.moduleCategory.{u + 1, u + 1} (ULift.{u + 1} ℤ))
          inferInstance inferInstance inferInstance inferInstance
      have hh := congrArg S.map hkillF
      rw [S.map_nsmul, S.map_id, S.map_zero] at hh
      simpa using congrArg (fun f : S.obj (T.obj P.F) ⟶ S.obj (T.obj P.F) ↦ f.hom x) hh
    have ht : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) (T.obj P.F) ∨
        ∃ p : ℕ, p.Prime ∧ CharP k p ∧
          Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) (T.obj P.F) p := by
      by_cases hrk : (r : k) = 0
      · exact Or.inr ⟨r, hr, (CharP.charP_iff_prime_eq_zero hr).mpr hrk,
          fun Ω _ _ s x ↦ ⟨1, by simpa using hstalk Ω s x⟩⟩
      · refine Or.inl ⟨fun Ω _ _ s x ↦ ⟨r, hr.pos, ?_, hstalk Ω s x⟩⟩
        simpa using (isUnit_iff_ne_zero.mpr hrk).map
          (Scheme.ΓSpecIso (.of k)).inv.hom
    exact ⟨hreverse ht, hforward⟩

end AlgebraicGeometry
