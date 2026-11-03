/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.TraceWeilComplex.TraceWeilComplex
public import WeilConjectures.AlgebraicGeometry.CompactTracePointObjects
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Group.TransferInstance
import WeilConjectures.CategoryTheory.FiniteFilteredGradedExactness
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.CategoryTheory.LocalizationStrictFiltration
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import WeilConjectures.CategoryTheory.LocalizationExactBoundary

import WeilConjectures.AlgebraicGeometry.LocalizationSheafExchange
import WeilConjectures.CategoryTheory.LocalizationClosedMate
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenExtensionProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCanonicalPullbackComposition
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CurrentCtfSixFunctorStability
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixOperationsPackage
import WeilConjectures.TraceFormula.FiniteFieldDatum.FrobeniusOpenSquare
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.Topology.Homeomorph.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget
import WeilConjectures.AlgebraicGeometry.UniversallyHomeomorphIntegral
import Mathlib.AlgebraicGeometry.Cover.Open
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
import WeilConjectures.Compactification.NagataCompactification

/-! # Open–closed additivity for finite-coefficient Frobenius correspondences

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-frobenius-and-rf/sk-i-global-additivity/_section.md and sk-i-global-additivity.proof.md
(blueprint: sk-i-global-additivity).

The restrictions use canonical pullback composition. The open and closed extensions are
actual derived sheaf functors. Their coefficient maps are normalized by the localization
counit and unit and by restriction to their support, including every iterate. The trace
is the existing perfect-complex categorical trace of sk-d-trace, valued in A through
the recorded geometric stalk and scalar-universe identification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.TraceOperations
open scoped CategoryTheory.Obj

namespace WeilConjectures.TraceWeilComplex

/-- Base change of a model morphism to the fixed algebraic closure.
Source: sk-i-global-additivity, first paragraph (blueprint: sk-i-global-additivity). -/
abbrev localizationGeometricMap (F : FiniteFieldDatum.{u})
    {Y₀ X₀ : Over (Spec (.of F.k₀))}
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (h₀ : Y₀ ⟶ X₀) :
    F.geometricFiber Y₀ ⟶ F.geometricFiber X₀ :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k)))).map h₀

/-- The base change of the model open immersion is an open immersion.
Source: sk-i-global-additivity, first paragraph (blueprint: sk-i-global-additivity).
Proof: localizationGeometricMap is the image under Over.pullback, hence the base change
of j₀ along the field extension. Open immersions are stable under base change. -/
theorem localizationGeometricOpen (F : FiniteFieldDatum.{u})
    {U₀ X₀ : Over (Spec (.of F.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] :
    IsOpenImmersion (localizationGeometricMap F j₀).left := by
  change IsOpenImmersion (pullback.map U₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k))) X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k))) j₀.left (𝟙 _) (𝟙 _)
    (by simp) (by simp))
  infer_instance

/-- Naturality of model Frobenius for a model morphism.
Source: sk-i-global-additivity.proof.md, restriction step
(blueprint: sk-i-global-additivity).
Proof: on affine sections power Frobenius commutes with every ring map, since
f(a^q)=f(a)^q. These equalities glue. Apply the base-change functor to the equality
of morphisms over the finite field. -/
theorem localizationModelFrobenius_commutes (F : FiniteFieldDatum.{u})
    {Y₀ X₀ : Over (Spec (.of F.k₀))}
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (h₀ : Y₀ ⟶ X₀) :
    localizationGeometricMap F h₀ ≫ modelFrobenius F X₀ =
      modelFrobenius F Y₀ ≫ localizationGeometricMap F h₀ := by
  unfold localizationGeometricMap modelFrobenius
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply Over.OverMorphism.ext
  exact Scheme.comp_iterateFrobenius F.prime h₀.left
    (F.model_characteristic X₀.hom) (F.model_characteristic Y₀.hom) F.a

/-- Naturality of every power of model Frobenius, including power zero.
Source: sk-i-global-additivity.proof.md, restriction step
(blueprint: sk-i-global-additivity).
Proof: naturality of absolute power Frobenius is the identity f(a^q)=f(a)^q on affine
sections. Base change preserves the resulting equality of morphisms over the finite field.
Induction on m, with associativity and the identity laws, gives the displayed equality. -/
theorem localizationModelFrobenius_natural (F : FiniteFieldDatum.{u})
    {Y₀ X₀ : Over (Spec (.of F.k₀))}
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (h₀ : Y₀ ⟶ X₀) (m : ℕ) :
    localizationGeometricMap F h₀ ≫ frobeniusPower (modelFrobenius F X₀) m =
      frobeniusPower (modelFrobenius F Y₀) m ≫ localizationGeometricMap F h₀ := by
  induction m with
  | zero => simp [frobeniusPower]
  | succ m hm =>
      simp only [frobeniusPower, ← Category.assoc, hm]
      rw [Category.assoc, localizationModelFrobenius_commutes, ← Category.assoc]

/-- Geometry of the two pieces, used as derived instance witnesses rather than extra
hypotheses of additivity. Source: sk-i-global-additivity.proof.md, geometry step
(blueprint: sk-i-global-additivity).
Proof: a finite affine cover by Noetherian spectra makes X₀ topologically Noetherian.
Its open U₀ is quasi-compact, so the open immersion is finite type. The closed immersion
is finite. Composition with the separated finite-type structure map gives the six
assertions. All persist after field base change; Nagata gives the compactifications. -/
theorem localizationModelGeometry (F : FiniteFieldDatum.{u})
    {U₀ Z₀ X₀ : Over (Spec (.of F.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left] :
    LocallyOfFiniteType U₀.hom ∧ QuasiCompact U₀.hom ∧ IsSeparated U₀.hom ∧
    LocallyOfFiniteType Z₀.hom ∧ QuasiCompact Z₀.hom ∧ IsSeparated Z₀.hom := by
  have : IsLocallyNoetherian X₀.left :=
    LocallyOfFiniteType.isLocallyNoetherian X₀.hom
  have : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  have : IsNoetherian X₀.left := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U₀.left :=
    j₀.left.isOpenEmbedding.isInducing.noetherianSpace
  have : LocallyOfFiniteType U₀.hom := by
    rw [← j₀.w]
    infer_instance
  have : IsSeparated U₀.hom := by
    rw [← j₀.w]
    infer_instance
  have : LocallyOfFiniteType Z₀.hom := by
    rw [← i₀.w]
    infer_instance
  have : QuasiCompact Z₀.hom := by
    rw [← i₀.w]
    infer_instance
  have : IsSeparated Z₀.hom := by
    rw [← i₀.w]
    infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

/-- Compactifiability after extension of the model's base field.
Source: sk-i-global-additivity.proof.md, compact-support step
(blueprint: sk-i-global-additivity).
Proof: separatedness and finite type are stable under field base change. The new base
is the spectrum of a field, hence qcqs. Apply thm-nagata-compactification to the structure
morphism. Only the existence proposition is used; no arbitrary geometric data are chosen. -/
theorem localizationModelCompactifiable (F : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of F.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom] :
    HasCompactification (F.geometricFiber X₀).hom := by
  change HasCompactification (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap F.k₀ F.k))))
  infer_instance

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {s : Scheme.{u}}

/-- Pull back a coefficient morphism through a Frobenius-commuting square. This is
inverse composition, equality transport, composition, then pullback of the given map.
Source: sk-i-global-additivity.proof.md, restrictions (blueprint: sk-i-global-additivity). -/
def localizationRestrictionCoefficient {Y X : Over s} (h : Y ⟶ X)
    (tX : X ⟶ X) (tY : Y ⟶ Y) (e : h ≫ tX = tY ≫ h)
    (K : TraceOperations.D Λ X.left) (v : (star Λ tX.left).obj K ⟶ K) :
    (star Λ tY.left).obj ((star Λ h.left).obj K) ⟶ (star Λ h.left).obj K :=
  (pullbackComposition Λ tY h).inv.app K ≫
    (starCongr (Λ := Λ) e.symm).hom.app K ≫
    (pullbackComposition Λ h tX).hom.app K ≫ (star Λ h.left).map v

/-- The restriction Weil complex with its specified coefficient map.
Source: sk-i-global-additivity, induced correspondences on j^*K and i^*K
(blueprint: sk-i-global-additivity). -/
def localizationRestriction {Y X : Over s} (h : Y ⟶ X) (tY : Y ⟶ Y)
    (W : WeilComplex Λ X) (e : h ≫ W.frobenius = tY ≫ h) : WeilComplex Λ Y where
  frobenius := tY
  complex := (star Λ h.left).obj W.complex
  coefficient := localizationRestrictionCoefficient h W.frobenius tY e W.complex W.coefficient

/-- A map of coefficient complexes compatible with the Frobenius coefficient morphisms.
Source: sk-i-global-additivity.proof.md, equivariant localization sequence
(blueprint: sk-i-global-additivity). -/
def LocalizationEquivariant {X : Over s} (t : X ⟶ X)
    (K L : TraceOperations.D Λ X.left)
    (v : (star Λ t.left).obj K ⟶ K) (w : (star Λ t.left).obj L ⟶ L) (a : K ⟶ L) : Prop :=
  (star Λ t.left).map a ≫ w = v ≫ a

/-- Open–closed trace additivity, with all induced correspondences and their normalized
restriction maps. Finite primary coefficients include the zero ring, and psi is arbitrary.

Source: sk-i-global-additivity, entire statement (blueprint: sk-i-global-additivity).
Proof following the DAG's seven steps:
1. Use localizationModelGeometry and sk-thm-sf-ctf-stability to put both restrictions and
   their open/closed extensions in D^b_ctf for the given arbitrary finite primary ring.
2. Model Frobenius is finite universally homeomorphic on all three schemes; its powers
   are proper. Pullback composition and naturality define the restricted coefficient maps
   and identify their iterates without using an inverse of psi.
3. Use sk-i-relative-frob (1)-(2) and pro-etale topological invariance, including nilpotent
   invariance, for the closed comparison; only the open Frobenius square is Cartesian.
4. Apply lem-trf-localization-filtered-pullback to the actual localization filtration.
   Its total is psi and its graded maps give the two extensions. The open unit and closed
   counit identify their restrictions with the displayed coefficient maps, hence also
   identify the fixed-point stalk maps. Composition compatibility gives every iterate.
5. Nagata and sk-thm-sf-package (4) express compact support by a proper pushforward of an
   open extension. lem-trf-filtered-derived-operation-lifts lifts these actual sheaf-derived
   operations and their unit/composition maps, producing a filtered global endomorphism.
6. sk-i-relative-frob (3) intertwines its two graded maps with the compact-support
   operators on U and Z; the closed immersion is proper, so its shriek equals its push.
7. det-compact-trace-perfect-at-point gives perfectness and hence right duals. Filtered
   additivity and conjugacy invariance in sk-p-trace give the displayed trace equation.
   No trace of a possibly nonprojective individual cohomology module is used. -/
theorem trace_globalOperator_eq_trace_add_trace
    (F : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ F.p)
    (A : Type u) [CommRing A] [Finite A]
    (_hprimary : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : IsTopologicalRing A := inferInstance
    let Λ := Profinite.continuousCoefficientRingObj A
    ∀ (O : Given Λ (Spec (.of F.k))) (P : GeometricOperations O)
      (U₀ Z₀ X₀ : Over (Spec (.of F.k₀)))
      [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
      (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]
      (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left] [IsReduced Z₀.left]
      (_hcompl : IsCompl (Set.range j₀.left.base) (Set.range i₀.left.base)),
    let g := localizationModelGeometry F j₀ i₀
    letI : LocallyOfFiniteType U₀.hom := g.1
    letI : QuasiCompact U₀.hom := g.2.1
    letI : IsSeparated U₀.hom := g.2.2.1
    letI : LocallyOfFiniteType Z₀.hom := g.2.2.2.1
    letI : QuasiCompact Z₀.hom := g.2.2.2.2.1
    letI : IsSeparated Z₀.hom := g.2.2.2.2.2
    letI := localizationModelCompactifiable F X₀
    letI := localizationModelCompactifiable F U₀
    letI := localizationModelCompactifiable F Z₀
    let j := localizationGeometricMap F j₀
    let i := localizationGeometricMap F i₀
    letI : IsOpenImmersion j.left := localizationGeometricOpen F j₀
    ∀ (K : ConstantModelConstructibleFiniteTor Λ (F.geometricFiber X₀).left)
      (ψ : FrobeniusCorrespondence F Λ X₀ K),
    let W := FrobeniusCorrespondence.toWeilComplex F ψ
    let WU := localizationRestriction j (modelFrobenius F U₀) W
      (localizationModelFrobenius_commutes F j₀)
    let WZ := localizationRestriction i (modelFrobenius F Z₀) W
      (localizationModelFrobenius_commutes F i₀)
    let J := (CondensedRing.openImmersionLowerShriek Λ j.left).mapDerivedCategory
    let I := push Λ i.left
    let adjJ :=
      CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction' Λ j.left
    let adjI := CondensedRing.derivedUpperStarLowerStarAdjunction Λ i.left
    ∃ (vJ : (star Λ W.frobenius.left).obj (J.obj WU.complex) ⟶ J.obj WU.complex)
      (vI : (star Λ W.frobenius.left).obj (I.obj WZ.complex) ⟶ I.obj WZ.complex),
    let WJ : WeilComplex Λ (F.geometricFiber X₀) := ⟨W.frobenius, J.obj WU.complex, vJ⟩
    let WI : WeilComplex Λ (F.geometricFiber X₀) := ⟨W.frobenius, I.obj WZ.complex, vI⟩
    (∃ KU : ConstantModelConstructibleFiniteTor Λ (F.geometricFiber U₀).left,
      KU.obj = WU.complex) ∧
    (∃ KZ : ConstantModelConstructibleFiniteTor Λ (F.geometricFiber Z₀).left,
      KZ.obj = WZ.complex) ∧
    (∃ KJ : ConstantModelConstructibleFiniteTor Λ (F.geometricFiber X₀).left,
      KJ.obj = WJ.complex) ∧
    (∃ KI : ConstantModelConstructibleFiniteTor Λ (F.geometricFiber X₀).left,
      KI.obj = WI.complex) ∧
    (∀ m : ℕ,
      WU.iterate m = localizationRestrictionCoefficient j
        (frobeniusPower W.frobenius m) (frobeniusPower WU.frobenius m)
        (localizationModelFrobenius_natural F j₀ m) K.obj (W.iterate m) ∧
      WZ.iterate m = localizationRestrictionCoefficient i
        (frobeniusPower W.frobenius m) (frobeniusPower WZ.frobenius m)
        (localizationModelFrobenius_natural F i₀ m) K.obj (W.iterate m) ∧
      LocalizationEquivariant (frobeniusPower W.frobenius m)
        WJ.complex W.complex (WJ.iterate m) (W.iterate m) (adjJ.counit.app K.obj) ∧
      LocalizationEquivariant (frobeniusPower W.frobenius m)
        W.complex WI.complex (W.iterate m) (WI.iterate m) (adjI.unit.app K.obj) ∧
      (star Λ (frobeniusPower WU.frobenius m).left).map (adjJ.unit.app WU.complex) ≫
          localizationRestrictionCoefficient j (frobeniusPower W.frobenius m)
            (frobeniusPower WU.frobenius m) (localizationModelFrobenius_natural F j₀ m)
            WJ.complex (WJ.iterate m) =
        WU.iterate m ≫ adjJ.unit.app WU.complex ∧
      localizationRestrictionCoefficient i (frobeniusPower W.frobenius m)
          (frobeniusPower WZ.frobenius m) (localizationModelFrobenius_natural F i₀ m)
          WI.complex (WI.iterate m) ≫ adjI.counit.app WZ.complex =
        (star Λ (frobeniusPower WZ.frobenius m).left).map (adjI.counit.app WZ.complex) ≫
          WZ.iterate m) ∧
    letI : IsAlgClosed F.k := IsAlgClosure.isAlgClosed F.k₀
    let H := internalFiniteDiscreteDerivedStalk A (𝟙 (Spec (.of F.k))) ⋙
      internalFiniteDiscreteStalkScalarLift A
    let PX := H.obj ((Comparisons.compactlySupported O (F.geometricFiber X₀)).obj K.obj)
    let PU := H.obj ((Comparisons.compactlySupported O (F.geometricFiber U₀)).obj WU.complex)
    let PZ := H.obj ((Comparisons.compactlySupported O (F.geometricFiber Z₀)).obj WZ.complex)
    ∃ (hPX : _root_.DerivedCategory.IsPerfectRingComplex PX)
      (hPU : _root_.DerivedCategory.IsPerfectRingComplex PU)
      (hPZ : _root_.DerivedCategory.IsPerfectRingComplex PZ),
    ∀ m : ℕ, 1 ≤ m →
    letI : IsProper (frobeniusPower W.frobenius m).left :=
      modelFrobeniusPower_isProper F X₀ m
    letI : IsProper (frobeniusPower WU.frobenius m).left :=
      modelFrobeniusPower_isProper F U₀ m
    letI : IsProper (frobeniusPower WZ.frobenius m).left :=
      modelFrobeniusPower_isProper F Z₀ m
    (_root_.DerivedCategory.perfectCategoricalTrace PX hPX
      (H.map (W.globalOperator O P m))).down =
      (_root_.DerivedCategory.perfectCategoricalTrace PU hPU
        (H.map (WU.globalOperator O P m))).down +
      (_root_.DerivedCategory.perfectCategoricalTrace PZ hPZ
        (H.map (WZ.globalOperator O P m))).down := by
  sorry

end WeilConjectures.TraceWeilComplex
