/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfExistence
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField

import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.GeoP1Adjunction.GeoP1Adjunction
import WeilConjectures.AlgebraicGeometry.Finite.FiniteProperLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportSheaves
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FormalClosedSupportGeneralField
import WeilConjectures.AlgebraicGeometry.Sf.SfAffineChartFactorizationGluing
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantStratifiedZariskiLocality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.OpenDirectImageCtf
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.Proper.ProperBoundedConstructible
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTorTest
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingSubcategoryUniverse
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
import WeilConjectures.AlgebraicGeometry.NativeAffinePullbackLine.NativeAffinePullbackLineCtf
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-!
# Finite-coefficient preservation by the supplied exceptional inverse image

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ctf-finite-geometric-restriction/
sk-prop-sf-rf-shriek-preservation/_section.md and its proof
sk-prop-sf-rf-shriek-preservation.proof.md in the same directory
(blueprint: sk-prop-sf-rf-shriek-preservation).

The exceptional functor and adjunction below are selected from the actual existence
statement, not assumed. The compactification is the existing fixed choice over the field.
The small object properties are the recorded Dctf property pulled back along the full
localizing inclusions. No new coefficient, constructibility or localizing notion is defined.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hk : Finite k ∨ IsAlgClosed k)
  (A : Type) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
  (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0)
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Select the functors and the adjunction supplied by `sk_prop_sf_existence` at the
existing chosen compactification, specializing its admissibility argument to A.
The chosen right adjoint together with its counit is determined up to unique compatible
isomorphism by that theorem. All selections below are projections of its witnesses;
no arbitrary functor or preservation hypothesis is supplied as input.
Source: latest blueprint sk-prop-sf-rf-shriek-preservation, first sentence, referring to
sk-prop-sf-existence (blueprint: sk-prop-sf-rf-shriek-preservation). -/
def finiteSuppliedAdjunctionData :
    Σ (F : (localizingClosureProEtale (Profinite.continuousMapRingObj.{u} A)
        X).FullSubcategory ⥤
      (localizingClosureProEtale (Profinite.continuousMapRingObj.{u} A) Y).FullSubcategory),
      Σ (G : (localizingClosureProEtale (Profinite.continuousMapRingObj.{u} A)
          Y).FullSubcategory ⥤
        (localizingClosureProEtale (Profinite.continuousMapRingObj.{u} A) X).FullSubcategory),
        F ⊣ G :=
  let Λ := Profinite.continuousMapRingObj.{u} A
  let hΛ : IsLocalizingAdmissibleCoefficient ell Λ :=
    Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, hA, ⟨Iso.refl _⟩⟩
  let c := AlgebraicGeometry.compactificationOverField k f
  let hex := sk_prop_sf_existence Λ ell k hk f hΛ c
  let h := hex.choose
  let hX := hex.choose_spec.choose
  let hY := hex.choose_spec.choose_spec.choose
  let _ := hX
  let _ := hY
  let hexG := hex.choose_spec.choose_spec.choose_spec.2.2
  let G := hexG.choose
  let s := hexG.choose_spec.choose
  let _ := s
  ⟨localizingLowerShriek Λ c.obj.obj h, G, hexG.choose_spec.choose_spec.2.2.choose⟩

/-- The compact-support functor in the supplied finite-coefficient adjunction.
Source: latest blueprint sk-prop-sf-rf-shriek-preservation, displayed adjunction
(blueprint: sk-prop-sf-rf-shriek-preservation). -/
abbrev finiteSuppliedLowerShriek := (finiteSuppliedAdjunctionData ell k hk A hA f).1

/-- The exceptional inverse image selected from the supplied existence theorem.
Source: latest blueprint sk-prop-sf-rf-shriek-preservation, first sentence
(blueprint: sk-prop-sf-rf-shriek-preservation). -/
abbrev finiteSuppliedUpperShriek := (finiteSuppliedAdjunctionData ell k hk A hA f).2.1

/-- The actual selected adjunction, whose Hom bijections are to be restricted.
Source: latest blueprint sk-prop-sf-rf-shriek-preservation, displayed adjunction
(blueprint: sk-prop-sf-rf-shriek-preservation). -/
abbrev finiteSuppliedShriekAdjunction :
    finiteSuppliedLowerShriek ell k hk A hA f ⊣ finiteSuppliedUpperShriek ell k hk A hA f :=
  (finiteSuppliedAdjunctionData ell k hk A hA f).2.2

end AlgebraicGeometry.ProEtale.CondensedRing
