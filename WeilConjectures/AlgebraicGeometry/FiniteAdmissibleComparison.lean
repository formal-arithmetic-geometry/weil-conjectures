/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.FiniteAdmissibleGeneration
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison

/-! # Finite admissible comparison with the etale derived category

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
`sk-prop-ctf-finite-comparison`, statement and proof
(blueprint: sk-prop-ctf-finite-comparison).

We use the existing ordinary fixed-scalar presentation with coefficients `ULift A`.
The pro-etale generators use the existing `DerivedCategory.constructibleFiniteTor`.
For finite coefficients on the standing qcqs schemes its etale-origin constructibility
agrees with intrinsic finite constant local models. All operation comparisons below
are natural isomorphisms in the ambient unbounded derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Finite admissible comparison, including generation of the entire etale category,
ambient coproducts, and the canonical operation comparisons.

Source: blueprint, sec-six-functors-basics/sk-prop-ctf-finite-comparison, both proof
paragraphs (blueprint: sk-prop-ctf-finite-comparison).

Proof: the generation helper applies the compact affine-etale detecting family and
the telescope construction, separately for finite and algebraically closed fields.
The restriction helper transports the Noetherian finite-Tor comparison through
coefficient-model realization equivalences, proves the generic localizing-image argument,
and uses generation to obtain the stated equivalence from the whole etale category.

The derived comparison is a left adjoint, hence preserves arbitrary coproducts.
Every standing k-morphism is locally of finite type and quasi-compact by cancellation
against its structure map. The unbounded direct-image theorem makes each component
of the specified canonical mate invertible; its naturality assembles these components
into a natural isomorphism. Use the canonical pullback comparison for pullback.
Finally derive the exact open-extension comparison and compose it with the direct-
image comparison for the proper part of the same compactification. Associativity
isomorphisms identify this composite with the two compact-support functors.
-/
theorem finiteAdmissibleComparison
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type u) [CommRing A] [Finite A] (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    CategoryTheory.localizingClosure
        (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) X ⊓
          _root_.DerivedCategory.finiteTorAmplitude _) = ⊤ ∧
    (∃ E : Etale.DerivedCategoryModule (ULift.{u + 1} A) X ≌
        (CategoryTheory.localizingClosure
          (DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)).FullSubcategory,
      Nonempty (E.functor ⋙ (CategoryTheory.localizingClosure
          (DerivedCategory.constructibleFiniteTor
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)).ι ≅
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory)) ∧
    (∀ I : Type v, Nonempty (PreservesColimitsOfShape (Discrete I)
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory)) ∧
    (∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
      (g : X ⟶ Y) [g.IsOver (Spec (.of k))],
      Nonempty
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).mapDerivedCategory ⋙
            (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).mapDerivedCategory ≅
          (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).mapDerivedCategory ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory) ∧
      ∃ e : (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).rightDerivedFunctor ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).mapDerivedCategory ≅
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory ⋙
            (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).rightDerivedFunctor,
        ∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} A) X,
          e.hom.app K = unboundedDirectImageComparisonMap (ULift.{u + 1} A) g K) ∧
    (∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f)
      [c.Z.Over (Spec (.of k))] [IsSeparated (c.Z ↘ Spec (.of k))]
      [LocallyOfFiniteType (c.Z ↘ Spec (.of k))] [QuasiCompact (c.Z ↘ Spec (.of k))]
      [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))] [QuasiCompact c.i],
      Nonempty
        (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) c ⋙
              (comparisonUpperStar
                (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).mapDerivedCategory ≅
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory ⋙
            ProEtale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1} A)) c)) := by
  have hgen := finiteAdmissibleGeneration k hbase ℓ hℓ A hA X
  have hrest := finiteAdmissibleRestriction k hbase ℓ hℓ A hA X
  have hnil : ∃ n : ℕ, (ℓ : ULift.{u + 1} A) ^ n = 0 := by
    obtain ⟨n, hn⟩ := hA
    refine ⟨n, (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).injective ?_⟩
    simpa only [map_pow, map_natCast, map_zero] using hn
  have hdir (T U : Scheme.{u}) [T.Over (Spec (.of k))]
      [U.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
      (g : T ⟶ U) [LocallyOfFiniteType g] [QuasiCompact g] :
      ∃ e : (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).rightDerivedFunctor ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) U).mapDerivedCategory ≅
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory ⋙
            (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).rightDerivedFunctor,
        ∀ K, e.hom.app K = unboundedDirectImageComparisonMap (ULift.{u + 1} A) g K := by
    have hi (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) T) :
        IsIso (unboundedDirectImageComparisonMap (ULift.{u + 1} A) g K) :=
      unboundedDirectImageComparison k hbase hℓ (ULift.{u + 1} A) hnil g K
    let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let S := (Etale.lowerStar C g).rightDerivedFunctor ⋙
      (comparisonUpperStar C U).mapDerivedCategory
    let R := (comparisonUpperStar C T).mapDerivedCategory ⋙
      (ProEtale.lowerStar C g).rightDerivedFunctor
    let e : S ≅ R := NatIso.ofComponents
      (fun K ↦ asIso (unboundedDirectImageComparisonMap (ULift.{u + 1} A) g K))
      (by
        intro K L f
        exact unboundedDirectImageComparisonMap_naturality (ULift.{u + 1} A) g f)
    exact ⟨e, fun _ ↦ rfl⟩
  refine ⟨hgen, hrest, ?_, ?_, ?_⟩
  · intro I
    let adj := (comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) X)
      |>.mapDerivedCategoryRightDerivedAdjunction
    exact ⟨adj.leftAdjoint_preservesColimits.preservesColimitsOfShape⟩
  · intro Y _ _ _ _ g _
    have : LocallyOfFiniteType (g ≫ (Y ↘ Spec (.of k))) := by
      rw [CategoryTheory.comp_over g (Spec (.of k))]
      infer_instance
    have : QuasiCompact (g ≫ (Y ↘ Spec (.of k))) := by
      rw [CategoryTheory.comp_over g (Spec (.of k))]
      infer_instance
    let : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (Y ↘ Spec (.of k))
    let : QuasiCompact g := QuasiCompact.of_comp g (Y ↘ Spec (.of k))
    exact ⟨⟨unboundedDirectImagePullbackIso (ULift.{u + 1} A) g⟩, hdir X Y g⟩
  · intro Y _ _ _ _ f _ c _ _ _ _ _ _ _
    obtain ⟨e, _⟩ := hdir c.Z Y c.g
    let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let jE := (Etale.openImmersionLowerShriek C c.i).mapDerivedCategory
    let jP := (ProEtale.openImmersionLowerShriek C c.i).mapDerivedCategory
    let pP := (ProEtale.lowerStar C c.g).rightDerivedFunctor
    let F := (comparisonUpperStar C X).mapDerivedCategory
    let G := (comparisonUpperStar C c.Z).mapDerivedCategory
    let ej : jE ⋙ G ≅ F ⋙ jP :=
      (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso C c.i) ≪≫
        Functor.mapDerivedCategoryCompIso _ _
    exact ⟨Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft jE e ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ej pP ≪≫
      Functor.associator _ _ _⟩

end AlgebraicGeometry.ProEtale
