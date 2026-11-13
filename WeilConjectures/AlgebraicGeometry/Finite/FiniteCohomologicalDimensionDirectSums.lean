/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
import all WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget

/-!
# Direct sums and finite cohomological dimension

Source: Stacks Project, Etale Cohomology, Tag 0F11.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- If `n ≥ 1` and `f` is quasi-compact, quasi-separated and of finite torsion étale
cohomological dimension, derived direct image on `ZMod n`-module étale sheaves commutes
with every set-indexed coproduct; for every qcqs scheme of finite torsion étale
cohomological dimension, derived global sections has the same property. The coefficient
ring is lifted by the canonical ring equivalence `ULift.ringEquiv` to the universe used
by the existing six-functor and derived-category interfaces. -/
theorem derivedDirectImage_and_globalSections_preserveCoproducts
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
      f.torsionEtaleCohomologicalDimension < ⊤ →
        ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
          (rightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) f)) ∧
      (∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X],
        X.torsionEtaleCohomologicalDimension < ⊤ →
          ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
            (rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) X)) := by
  have : NeZero n := ⟨by omega⟩
  let Λ := ULift.{u + 1} (ZMod n)
  constructor
  · intro X Y f _ _ hf I
    have hdim : HasFiniteCohomologicalDimensionMorphism Λ f := by
      obtain ⟨a, ⟨d, rfl, hd⟩, _⟩ := sInf_lt_iff.mp hf
      refine ⟨d, fun F q hq ↦ ?_⟩
      obtain ⟨q, rfl⟩ : ∃ k : ℕ, q = (k : ℤ) := ⟨q.toNat, by omega⟩
      let S := sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      have hF : (S.obj F).IsTorsion :=
        (Scheme.isTorsionModuleSheaf_iff_isTorsion F).mp inferInstance
      have hz := hd (S.obj F) hF q hq
      obtain ⟨e⟩ := nonempty_higherDirectImage_forget_iso Λ f q F
      have hz' := hz.of_iso e
      let T := sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      have hM : IsZero (higherDirectImage Λ f q F) := by
        rw [IsZero.iff_id_eq_zero] at hz' ⊢
        exact T.map_injective (by simpa using hz')
      exact hM.of_iso (homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ f F q)
    exact CategoryTheory.preservesCoproducts_of_small _
      (preservesCoproducts_rightDerivedLowerStar Λ f hdim) I
  · intro X _ _ hX I
    have hdim : HasFiniteCohomologicalDimension Λ X := by
      obtain ⟨a, ⟨d, rfl, hd⟩, _⟩ := sInf_lt_iff.mp hX
      refine ⟨d, fun F q hq ↦ ?_⟩
      obtain ⟨q, rfl⟩ : ∃ k : ℕ, q = (k : ℤ) := ⟨q.toNat, by omega⟩
      let S := sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      have hF : (S.obj F).IsTorsion :=
        (Scheme.isTorsionModuleSheaf_iff_isTorsion F).mp inferInstance
      have hz : Subsingleton ((cohomology AddCommGrpCat.{u + 1} X q).obj
          ((DerivedCategory.singleFunctor _ 0).obj (S.obj F))) :=
        hd (S.obj F) hF q (by exact_mod_cast hq)
      obtain ⟨e⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso X Λ q
      have : Subsingleton ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
          ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) :=
        @Function.Injective.subsingleton _ _ _
          (e.app F).addCommGroupIsoToAddEquiv.injective hz
      exact ModuleCat.isZero_of_subsingleton _
    exact CategoryTheory.preservesCoproducts_of_small _
      (preservesCoproducts_rightDerivedGlobalSections Λ X hdim) I

end AlgebraicGeometry.Etale
