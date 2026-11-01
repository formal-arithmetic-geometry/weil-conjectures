/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarModelImmersionExtension
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Closed direct image with condensed coefficients

The same proof applies to every commutative condensed coefficient ring. The ambient
functor is the total right derived functor of the specified module-object direct image;
its restriction uses finite constant scalar-model constructibility.

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-closed-unit,
prop-sf-closed-unit-all-stages, order 3188
(blueprint: prop-sf-closed-unit-all-stages).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

/-- Closed direct image is fully faithful on the ambient unbounded derived category
and admits a fully faithful restriction to bounded constructible complexes. Every
right-adjoint unit for either functor is invertible; the ambient right adjoint exists.
This applies uniformly to finite, integral, rational and algebraically closed condensed
coefficients. No field, prime or coefficient-stage hypothesis is needed.

Source: current Weil blueprint, prop-sf-closed-unit-all-stages and its proof, order 3188.
(blueprint: prop-sf-closed-unit-all-stages).

Proof: the closed ring-sheaf counit is invertible, so module direct image is fully
faithful. Exact pullback implies that it preserves K-injective complexes, and hence
its total right derived functor is fully faithful. Exactness identifies its homology
with direct image of homology. Extend a constructible stratification by the complementary
open with zero scalar model; this preserves bounded constructibility. Restrict to the
full subcategories. The support-kernel adjunction supplies the ambient right adjoint.
Finally the fully faithful left-adjoint criterion makes each actual unit invertible. -/
theorem closedUnitAllStages
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z X : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (lowerStar Λ i).rightDerivedFunctor.Full ∧
    (lowerStar Λ i).rightDerivedFunctor.Faithful ∧
    (∀ (G : DerivedCategory (supportModules Λ X) ⥤
        DerivedCategory (supportModules Λ Z))
      (adj : (lowerStar Λ i).rightDerivedFunctor ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) ∧
    (∃ G : DerivedCategory (supportModules Λ X) ⥤ DerivedCategory (supportModules Λ Z),
      Nonempty ((lowerStar Λ i).rightDerivedFunctor ⊣ G)) ∧
    ∃ F : ConstantModelBoundedConstructible Λ Z ⥤ ConstantModelBoundedConstructible Λ X,
      Nonempty (F ⋙ (constantModelBoundedConstructible Λ X).ι ≅
        (constantModelBoundedConstructible Λ Z).ι ⋙ (lowerStar Λ i).rightDerivedFunctor) ∧
      F.Full ∧ F.Faithful ∧
      (∀ (G : ConstantModelBoundedConstructible Λ X ⥤
          ConstantModelBoundedConstructible Λ Z) (adj : F ⊣ G),
        ∀ Q, IsIso (adj.unit.app Q)) := by
  classical
  let O : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hO : Set.range O.ι = (Set.range i)ᶜ := Subtype.range_coe
  have hOi : Set.range i.base = (Set.range O.ι.base)ᶜ := by
    rw [hO, compl_compl]
  obtain ⟨hexact, hcounit⟩ := AlgebraicGeometry.ProEtale.closed_operations Λ O.ι i hO
  have := hexact
  have := hcounit
  have := (upperStarLowerStarAdjunction Λ i).fullyFaithfulROfIsIsoCounit.full
  have := (upperStarLowerStarAdjunction Λ i).fullyFaithfulROfIsIsoCounit.faithful
  have := (upperStarLowerStarAdjunction Λ i).preservesKInjectiveComplexes
  have hfull : (lowerStar Λ i).rightDerivedFunctor.Full := inferInstance
  have hfaithful : (lowerStar Λ i).rightDerivedFunctor.Faithful := inferInstance
  have hmodel := (AlgebraicGeometry.ProEtale.immersion_assertions Λ O.ι i hO).2.2.2.2.2.1
  have hpres (K : ConstantModelBoundedConstructible Λ Z) :
      constantModelBoundedConstructible Λ X ((lowerStar Λ i).rightDerivedFunctor.obj K.obj) := by
    have hb := (lowerStar Λ i).bounded_mapDerivedCategory_obj K.property.1
    have hb' : DerivedCategory.TStructure.t.bounded
        ((lowerStar Λ i).rightDerivedFunctor.obj K.obj) := by
      exact DerivedCategory.TStructure.t.bounded.prop_of_iso
        (((lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory).app K.obj).symm hb
    refine ⟨hb', fun n ↦ ?_⟩
    have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      (((lowerStar Λ i).rightDerivedFunctorHomologyFunctorIso n).app K.obj)
      (hmodel _ (K.property.2 n))
  let F := (constantModelBoundedConstructible Λ X).lift
    ((constantModelBoundedConstructible Λ Z).ι ⋙ (lowerStar Λ i).rightDerivedFunctor) hpres
  have hF : F ⋙ (constantModelBoundedConstructible Λ X).ι ≅
      (constantModelBoundedConstructible Λ Z).ι ⋙ (lowerStar Λ i).rightDerivedFunctor :=
    Iso.refl _
  have : F.Full := Functor.Full.of_comp_faithful_iso hF
  have : F.Faithful := Functor.Faithful.of_comp_iso hF
  refine ⟨hfull, hfaithful, ?_, ?_, F, ⟨hF⟩, inferInstance, inferInstance, ?_⟩
  · intro G adj Q
    have := adj.unit_isIso_of_L_fully_faithful
    infer_instance
  · let adj := closedSupportDerivedAdjunction Λ i O.ι hOi
    exact ⟨_, ⟨adj.ofNatIsoLeft (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.symm⟩⟩
  · intro G adj Q
    have := adj.unit_isIso_of_L_fully_faithful
    infer_instance

end WeilConjectures
