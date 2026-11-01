/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.ProperBaseChange.CondensedQbarFieldEvaluationLinearity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.AdjunctionSquareExchange
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.Compactification.BaseChange
import WeilConjectures.AlgebraicGeometry.ClopenLocalization.ProEtaleClopenUnboundedDerivedLocalization
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.Compactification.Dense
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.ProperCoproduct
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Finite clopen decomposition of condensed compact-support complexes

Source: latest blueprint, sec-deligne-laumon-general/sk-p-dl-general-relative-line/
lem-zl-affine-curve-hc2-purity.proof.md, second paragraph and empty-curve clause
(blueprint: lem-zl-condensed-clopen-compact-decomposition).

## Main definitions

`componentInclusion` and `boundedInclusion` give the canonical component maps.
`PointTransport` and `OpenTransport` specify the actual geometric exchange;
`compactTransport` and `action` compose the proper mate, open exchange and Weil map.

## Main statements

`condensed_clopen_compact_decomposition` states the natural biproduct decomposition,
its geometric Frobenius compatibility and its empty-index case.

The component maps are normalized by the open adjunction counit. The transport
records below specify the point-section comparison and the open adjunction mate;
they never supply an unconstrained endomorphism called Frobenius.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedClopenCompact

/-- Exact pullback, with the canonical condensed scalar comparison.
Source: the node's restriction convention
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev pull (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) f).mapDerivedCategory

/-- The same geometric Frobenius map, using the recorded Galois construction directly.
This presentation also applies before installing the inherited finite-type instances.
Source: def-weil-frobenius-detailed, formula for geometricFrobenius.hom
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev schemeFrobenius (D : FiniteFieldDatum.{u}) (X : Over (Spec (.of D.k₀))) :=
  D.galoisMap X.hom (by
    letI := Fintype.ofFinite D.k₀
    exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)

/-- The canonical inclusion of the geometric base change of an arithmetic component.
Source: the node's X_i and j_i conventions
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def geometricInclusion (D : FiniteFieldDatum.{u})
    {U X : Over (Spec (.of D.k₀))} (j : U ⟶ X) :
    pullback U.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ⟶
      pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j).left

/-- The common compactification obtained by base changing the arithmetic one.
Source: the node's proof, steps 1--2
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev geometricCompactification (D : FiniteFieldDatum.{u})
    {X : Over (Spec (.of D.k₀))} (c : Compactification X.hom) :=
  c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Frobenius on the compactification is the actual base-change Galois map.
Source: the node's proof, step 6
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev compactificationFrobenius (D : FiniteFieldDatum.{u})
    {X : Over (Spec (.of D.k₀))} (c : Compactification X.hom) :=
  D.galoisMap c.g (by
    letI := Fintype.ofFinite D.k₀
    exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)

end WeilConjectures.CondensedClopenCompact
