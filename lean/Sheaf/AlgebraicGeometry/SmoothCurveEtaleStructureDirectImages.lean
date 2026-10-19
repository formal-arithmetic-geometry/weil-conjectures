/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.EtaleQuasiCoherentDescent
import Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback
import Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Sheaf.AlgebraicGeometry.LeraySpectralSequence
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting

/-! # Structure-sheaf direct images for smooth proper curves

Source: Stacks Project, curves.tex, Tag 0GKA, (a),(b), and etale-cohomology.tex,
Tag 03P2 (blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images).

Linearity is expressed on the canonical local cohomology classes generating the
higher direct image. This specifies the natural scalar action without replacing
it by a freely chosen module structure on an additive sheaf.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

/-- Localized structure coefficients over an etale base object.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images). -/
noncomputable abbrev curveLocalStructure {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale) :=
  (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj X.etaleAdditiveSheaf

/-- Localization identifies a coefficient section with a lifted function.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images). -/
noncomputable def curveLocalFunction {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
    (T : (pullback U.hom f).Etale)
    (x : (curveLocalStructure f U).obj.obj (op T)) : ULift.{u + 1} Γ(T.left, ⊤) :=
  (((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    (pullback.snd U.hom f) inferInstance).hom.app X.etaleAdditiveSheaf).hom.app (op T)) x

/-- The normalization characterizing multiplication by a base function on local coefficients.
All etale test objects and all sections occur, so the endomorphism is determined uniquely.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images). -/
def IsCurveLocalScalar {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
    (a : Γ(U.left, ⊤)) (μ : curveLocalStructure f U ⟶ curveLocalStructure f U) : Prop :=
  ∀ (T : (pullback U.hom f).Etale) (x : (curveLocalStructure f U).obj.obj (op T)),
    curveLocalFunction f U T (μ.hom.app (op T) x) =
      ULift.up (@id Γ(T.left, ⊤) ((T.hom ≫ pullback.fst U.hom f).appTop a) *
        (curveLocalFunction f U T x).down)

/-- Action of the specified local coefficient endomorphism on restricted abelian cohomology.
Source: Stacks Project, Tags 03P2 and 03Q8
(blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images). -/
noncomputable def curveLocalCohomologyMap {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
    (μ : curveLocalStructure f U ⟶ curveLocalStructure f U) :
    rawAffineRestrictedCohomology f 1 X.etaleAdditiveSheaf U ⟶
      rawAffineRestrictedCohomology f 1 X.etaleAdditiveSheaf U :=
  (cohomology AddCommGrpCat.{u + 1} (pullback U.hom f) 1).map
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map μ))

/-- The structural direct image is the base structure sheaf, and the first abelian higher
image is the associated sheaf of a finite locally free module, with its natural scalars.
The last two clauses express module-linearity: multiplication is uniquely prescribed on
all localized coefficient sections; its cohomological action commutes with the displayed
isomorphism on canonical local classes. These classes locally generate the higher image.
No module action on the higher image is assumed or chosen arbitrarily.

Source: Stacks Project, curves.tex, Tag 0GKA, (a),(b), smooth specialization;
etale-cohomology.tex, Tag 03P2
(blueprint: lem-weil-pbc-smooth-curve-etale-structure-direct-images).

Proof:
1. Smoothness gives flatness, local finite presentation and geometrically reduced fibres.
   Properness gives finite presentation. The nonempty geometrically connected proper
   fibres have H0 equal to their residue fields (lem-pc-h0-geom-connected).
2. Apply perfect_derivedDirectImage_baseChange, exists_flat_derived_structure_unit and
   perfect_degreeZero_fibre_criterion. Zariski-locally the direct image complex splits
   as the structure module in degree zero plus a perfect positive-amplitude complex.
3. Fibres are Noetherian curves. Cohomology above dimension one vanishes, so
   exists_finiteFreeResidueModel makes the positive summand locally finite free in
   degree one. Its H1 is a global finite locally free module E, with variable local rank.
4. Derived base change and the affine Leray edge give compatible identifications
   H1(X_V,O) = Gamma(V,v*E) for affine etale V. Composition of adjunction units proves
   restriction compatibility; moduleCohomologyFMap_independent fixes the cohomology maps.
5. Apply exists_qcoherentCohomologyComparisonPullback and the higher-image-presheaf
   theorem to the same lifted coefficients. Coefficient naturality for multiplication
   proves the scalar equation on raw classes, through rawRestrictedCohomologyComparison.
6. Glue the compatible affine identifications by etale quasi-coherent descent and the
   locally bijective sheafification criterion. Linearity descends because raw classes
   locally generate. The degree-zero map is the structural function pullback, bijective
   on affine etale objects, hence an isomorphism by affine covers. Empty bases and rank
   zero need no separate nonemptiness or positive-rank assumptions. -/
theorem smooth_curve_etale_structure_direct_images {X S : Scheme.{u}}
    [CompactSpace S] [IsLocallyNoetherian S] (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1) :
    IsIso (Scheme.etaleAdditiveSheafToLowerStar f) ∧
      ∃ (E : S.Modules) (_ : E.IsFiniteLocallyFree) (_ : E.IsQuasicoherent)
        (e : (DerivedCategory.Plus.homologyFunctor
          (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) 1).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj X.etaleAdditiveSheaf)) ≅
          Scheme.Modules.liftedCoherentEtaleSheaf E),
        ∀ (U : S.Etale) (a : Γ(U.left, ⊤)),
          ∃ μ : curveLocalStructure f U ⟶ curveLocalStructure f U,
            IsCurveLocalScalar f U a μ ∧
            ∀ (z z' : (abelianHigherDirectImageRawPresheaf f 1
                X.etaleAdditiveSheaf).obj (op U)),
              rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z' =
                curveLocalCohomologyMap f U μ
                  (rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z) →
              e.hom.hom.app (op U)
                  (abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U z') =
                ULift.up (a • @id Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤)
                  (e.hom.hom.app (op U)
                    (abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U z)).down) := by
  sorry

end AlgebraicGeometry.Etale
