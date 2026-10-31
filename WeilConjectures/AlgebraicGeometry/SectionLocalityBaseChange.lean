/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.SectionLocalComparisonData
import all WeilConjectures.AlgebraicGeometry.SectionExceptionalFibreCoherence

/-! # Cartesian base change for counit-normalized section locality -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  rightDerivedUpperShriek rightDerivedUpperShriekAdjunction
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem sectionLocality_formula
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (h : U ⟶ X) [Etale h] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (f : X ⟶ B) [HasCompactification f] (f' : U ⟶ B) [HasCompactification f']
    (hf : h ≫ f = f') (s : B ⟶ X) (s' : B ⟶ U) (hs : s' ≫ h = s) :
    (SectionLocalDualizingComparisons.sectionLocality A h f f' hf s s' hs).hom =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' h s hs.symm).hom.app _ ≫
        (ordinaryFinitePullback A s').map
          (sectionStructuralLocalityIso A h f f' hf).hom := by
  subst f'
  let E := existsUnique_etaleAmbientAdjointLocalityIso A h f
    (HasCompactification.compactification f) (HasCompactification.compactification (h ≫ f))
    (rightDerivedUpperShriek A f) (rightDerivedUpperShriek A (h ≫ f))
    (rightDerivedUpperShriekAdjunction A f) (rightDerivedUpperShriekAdjunction A (h ≫ f))
  have he : Classical.choose E = E.exists.choose :=
    (E.choose_spec.2 _ E.exists.choose_spec).symm
  simp only [SectionLocalDualizingComparisons.sectionLocality, sectionStructuralLocalityIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, he]
  rfl

/-- Counit-normalized etale section locality commutes with Cartesian base change.
Source: orientation-charts Step 3, compatibility of the pulled-back ingredients.
(blueprint: lem-trf-section-locality-base-change).
Proof: identify sectionLocality with section pullback of the uniquely counit-normalized
ambient locality isomorphism, using uniqueness. Ambient locality base change gives
the middle square. Naturality moves the locality map through the section pullback
compositor, and the section-locality compositor pasting law gives the outer square.
A final compositor naturality equation gives exactly the two section maps displayed.
No smoothness or nonempty hypothesis is required. -/
theorem sectionLocality_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X B U' X' B' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    [IsNoetherian U'] [IsNoetherian X'] [IsNoetherian B']
    (u : U ⟶ X) (f : X ⟶ B) (u' : U' ⟶ X') (f' : X' ⟶ B')
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [Etale u'] [IsSeparated u'] [LocallyOfFiniteType u'] [QuasiCompact u']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f']
    (f₁ : U ⟶ B) (hf₁ : u ≫ f = f₁)
    (f₁' : U' ⟶ B') (hf₁' : u' ≫ f' = f₁')
    [HasCompactification f₁] [HasCompactification f₁']
    [QuasiCompact f'] [QuasiCompact f₁']
    (v : B' ⟶ B) (r : X' ⟶ X) (r₁ : U' ⟶ U)
    (sq : IsPullback r f' f v) (sqU : IsPullback r₁ u' u r)
    (sq₁ : IsPullback r₁ f₁' f₁ v)
    (s : B ⟶ X) (s' : B' ⟶ X') (s₁ : B ⟶ U) (s₁' : B' ⟶ U')
    (hs : s' ≫ r = v ≫ s) (hs₁ : s₁' ≫ r₁ = v ≫ s₁)
    (hu : s₁ ≫ u = s) (hu' : s₁' ≫ u' = s') :
    (ordinaryFinitePullback A v).map
        (SectionLocalDualizingComparisons.sectionLocality A u f f₁ hf₁ s s₁ hu).hom ≫
      SectionComparisonArrows.sectionMap A f₁ f₁' v r₁ sq₁ s₁ s₁' hs₁ =
    SectionComparisonArrows.sectionMap A f f' v r sq s s' hs ≫
      (SectionLocalDualizingComparisons.sectionLocality A u' f' f₁' hf₁' s' s₁' hu').hom := by
  have hd := structural_locality_baseChange A u f u' f' f₁ hf₁ f₁' hf₁'
    v r r₁ sq sqU sq₁
  have hc := section_pullback_locality_comp A v s s' s₁ s₁' u u' r r₁
    hs.symm hs₁.symm hu hu' sqU.w (dualizingComplex A f)
  have hn' := ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v s₁).symm ≪≫
    leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s₁' r₁ (v ≫ s₁) hs₁.symm).hom.naturality
    (sectionStructuralLocalityIso A u f f₁ hf₁).hom
  dsimp only [ordinaryFinitePullback, sectionInvariant] at *
  simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    NatTrans.comp_app, Category.assoc] at hn'
  simp only [sectionCoherencePullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Category.assoc] at hd hc
  simp only [sectionLocality_formula, SectionComparisonArrows.sectionMap,
    Functor.map_comp, Category.assoc, ordinaryFinitePullback, sectionInvariant,
    Iso.app_hom, Iso.app_inv]
  erw [reassoc_of% hn']
  rw [← Functor.map_comp, ← hd]
  simp only [Functor.map_comp]
  simp only [Functor.map_comp, Category.assoc] at hc
  rw [reassoc_of% hc]
  have hn'' := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    s₁' u' s' hu'.symm).hom.naturality (dualizingComplexBaseChangeMap A sq)
  simp only [Functor.comp_map] at hn''
  erw [← reassoc_of% hn'']

end AlgebraicGeometry.Etale
