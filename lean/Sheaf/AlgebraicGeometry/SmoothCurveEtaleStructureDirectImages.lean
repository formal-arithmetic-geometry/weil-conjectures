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
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Curve.CanonicalAdditiveCohomologyComparison
import Sheaf.AlgebraicGeometry.ProperFlatGlobalSections
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Sheaf.AlgebraicGeometry.FlatCurveDerivedStructureModel
import Sheaf.AlgebraicGeometry.CurveAffineEdge
import Sheaf.AlgebraicGeometry.UnitAffineCohomologyEtaleRealization
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

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

private noncomputable def localStructureIso {X S : Scheme.{u}}
    (f : X ⟶ S) (U : S.Etale) :
    curveLocalStructure f U ≅ (pullback U.hom f).etaleAdditiveSheaf :=
  (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
    (pullback.snd U.hom f) inferInstance).app X.etaleAdditiveSheaf

private theorem exists_localScalar {X S : Scheme.{u}}
    (f : X ⟶ S) (U : S.Etale) (a : Γ(U.left, ⊤)) :
    ∃ μ : curveLocalStructure f U ⟶ curveLocalStructure f U,
      IsCurveLocalScalar f U a μ := by
  let e := localStructureIso f U
  let m := Scheme.Modules.etaleAdditiveSmul (pullback U.hom f)
    ((pullback.fst U.hom f).appTop a)
  refine ⟨e.hom ≫ m ≫ e.inv, ?_⟩
  intro T x
  have hm : (e.hom ≫ m ≫ e.inv) ≫ e.hom = e.hom ≫ m := by simp
  have hx := congrArg (fun k ↦ k.hom.app (op T) x) hm
  change curveLocalFunction f U T
      ((e.hom ≫ m ≫ e.inv).hom.app (op T) x) = _ at hx
  rw [hx]
  apply ULift.ext
  change (curveLocalFunction f U T x).down *
      (@id Γ(T.left, ⊤) (T.hom.appTop ((pullback.fst U.hom f).appTop a))) = _
  rw [Scheme.Hom.comp_appTop]
  exact mul_comm _ _

private theorem structure_appTop_bijective {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f] :
    Function.Bijective f.appTop := by
  have hred (s : S) : GeometricallyReduced (f.fiberToSpecResidueField s) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  have hconn (s : S) : GeometricallyConnected (f.fiberToSpecResidueField s) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  have hu := (isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers
    f hred hconn).1
  have hi := (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso f).1
  have hs : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
    rw [← (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso f).2]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ⊤)

private theorem structure_etale_isIso {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f] :
    IsIso (Scheme.etaleAdditiveSheafToLowerStar f) := by
  have hnat : IsIso (Scheme.etaleAdditiveSheafToLowerStar f).hom := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact ULift.map_bijective.mpr
      (structure_appTop_bijective (pullback.fst U.unop.hom f))
  let F := sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : IsIso (F.map (Scheme.etaleAdditiveSheafToLowerStar f)) := hnat
  exact isIso_of_reflects_iso _ F

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
1. Proper-flat global sections makes the adjoint structure map invertible for a
   smooth proper map with geometrically connected fibres. Compose with the canonical
   pulled-back unit isomorphism. Evaluation on top sections gives the structural
   ring-map bijection. Apply this after every etale base change to prove degree zero.
2. The same argument on residue-field fibres supplies the constants hypothesis of
   flatCurve_derivedStructure_model. Fibre dimension one supplies its dimension bound.
   Its H1 is the required quasi-coherent finite locally free module E.
3. Transport the model's local splitting through the equivalence between modules
   over an open site and modules on the open subscheme. Identify shifted degree-zero
   singles with degree-one singles. Flatness of the unit makes the tensor counit and
   canonical derived base change invertible. The coherent affine edge theorem gives
   simultaneous linear comparisons with sections of pullbacks of E.
4. Normalize those comparisons through pullback symmetry and the tensor-unit maps,
   then apply affine-cohomology etale realization. Coefficient naturality and the
   section-normalized restriction isomorphisms transport its scalar-class formula
   to actual additive structural functions.
5. Conjugate multiplication on localized structural functions through localization
   to construct each required local endomorphism. Its values on every test section
   are the prescribed scalar values, so the normalized formula applies. Empty schemes
   and rank zero are included throughout. -/
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
  classical
  let : ∀ Y : Scheme.{u}, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    fun Y ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let : ∀ U : S.Opens, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) :=
    fun U ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))
  have hconstants (s : S) : IsIso (f.fiberToSpecResidueField s).appTop := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    have : IsProper (f.fiberToSpecResidueField s) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField]
      infer_instance
    have : Smooth (f.fiberToSpecResidueField s) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField]
      infer_instance
    have : GeometricallyConnected (f.fiberToSpecResidueField s) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField]
      infer_instance
    exact structure_appTop_bijective (f.fiberToSpecResidueField s)
  obtain ⟨hperfect, hzero, hqc, hfree, hsplit, hvanish, hbase⟩ :=
    flatCurve_derivedStructure_model.{u, u + 1} f (fun s ↦ (hdim s).le) hconstants
  have : (derivedStructureH1.{u, u + 1} f).IsQuasicoherent := hqc
  have : (derivedStructureH1.{u, u + 1} f).IsFiniteLocallyFree := hfree
  obtain ⟨b, hb⟩ := exists_curve_coherentEdge.{u, u + 1} f hzero hsplit
  have : (coherentEdgeCohomology.{u, u + 1} f
      (SheafOfModules.unit X.ringCatSheaf) 1).IsQuasicoherent := by
    unfold coherentEdgeCohomology coherentEdgeK topDegreeDerivedImage globalLerayImage
    change (derivedStructureH1.{u, u + 1} f).IsQuasicoherent
    exact hqc
  have : (coherentEdgeCohomology.{u, u + 1} f
      (SheafOfModules.unit X.ringCatSheaf) 1).IsFiniteLocallyFree := by
    unfold coherentEdgeCohomology coherentEdgeK topDegreeDerivedImage globalLerayImage
    change (derivedStructureH1.{u, u + 1} f).IsFiniteLocallyFree
    exact hfree
  obtain ⟨e, he⟩ := Scheme.Modules.exists_unitAffineCohomologyEtaleRealization
    f (coherentEdgeCohomology.{u, u + 1} f
      (SheafOfModules.unit X.ringCatSheaf) 1) b hb
  refine ⟨structure_etale_isIso f,
    coherentEdgeCohomology.{u, u + 1} f (SheafOfModules.unit X.ringCatSheaf) 1,
    inferInstance, inferInstance, e, ?_⟩
  intro U a
  obtain ⟨μ, hμ⟩ := exists_localScalar f U a
  exact ⟨μ, hμ, he U a μ hμ⟩

end AlgebraicGeometry.Etale
