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
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import WeilConjectures.DeligneLaumon.CondensedClopenCompact.CondensedClopenCompactCounit
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition

public import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

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

/-- Ordinary unbounded derived modules over the recorded pulled-back condensed Qbar ring.
Source: the node's coefficient convention
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev DMod (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell) X))

/-- Exact pullback, with the canonical condensed scalar comparison.
Source: the node's restriction convention
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev pull (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) f).mapDerivedCategory

/-- Total derived proper direct image, computed on K-injective resolutions.
Source: the compact-support construction in the node's proof, step 4
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev push (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell) f).rightDerivedFunctor

/-- Exact extension by zero on all integer-indexed complexes.
Source: the node's proof, step 3
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev extension (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :=
  (ProEtale.CondensedRing.openImmersionLowerShriek
    (Profinite.padicAlgClRingObj ell) j).mapDerivedCategory

/-- Composition of exact derived pullbacks, retaining the published scalar normalization.
Source: the node's proof, steps 3 and 6
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def pullComp (ell : ℕ) [Fact ell.Prime] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull ell (f ≫ g) ≅ pull ell g ⋙ pull ell f :=
  Functor.mapDerivedCategoryNatIso
    (ProEtale.CondensedRing.upperStarComp (Profinite.padicAlgClRingObj ell) f g) ≪≫
  Functor.mapDerivedCategoryCompIso _ _

/-- The exact-derived open adjunction is the published levelwise adjunction.
Source: the node's proof, step 3
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
abbrev openAdj (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] : extension ell j ⊣ pull ell j :=
  ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ell) j

/-- The square comparison is induced by the two composition isomorphisms.
Source: the node's proof, step 6
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def pullSquare (ell : ℕ) [Fact ell.Prime] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h : g' ≫ f = f' ≫ g) :
    pull ell g ⋙ pull ell f' ≅ pull ell f ⋙ pull ell g' :=
  (pullComp ell f' g).symm ≪≫
    eqToIso (congrArg (fun a ↦ pull ell a) h.symm) ≪≫ pullComp ell g' f

/-- The exact-derived pullback/total-derived pushforward adjunction.
Source: the node's proof, steps 4 and 6
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def pullPushAdj (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull ell f ⊣ push ell f :=
  (ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction
    (Profinite.padicAlgClRingObj ell) f).ofNatIsoLeft
      (ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (Profinite.padicAlgClRingObj ell) f)

/-- The proper exchange is precisely the unit--square--counit mate.
Source: the node's proof, step 6
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def properExchange (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (gx : X ⟶ X) (gy : Y ⟶ Y) (h : gx ≫ f = f ≫ gy) :
    push ell f ⋙ pull ell gy ⟶ pull ell gx ⋙ push ell f :=
  Adjunction.squareExchange (pullPushAdj ell f) (pullPushAdj ell f)
    (pull ell gy) (pull ell gx) (pullSquare ell h)

/-- A point transport in the fixed Qbar coordinates is the actual section comparison.
The equality specifies its underlying additive map after the canonical scalar cancellation.
Source: the node's proof, step 7; geometric-field evaluation and its scalar-linearity theorem
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
structure PointTransport (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] (sigma : k ≃+* k) where
  ordinary : ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell ≅
    ProEtale.CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (Spec.map (CommRingCat.ofHom sigma.toRingHom)) ⋙
        ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell
  normalization : ∀ M,
    ((ordinary.hom.app M ≫
      (ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell).map
        ((Mod.extendScalarsIsoComapInv (ProEtale.condensedPullbackHom
          (Profinite.padicAlgClRingObj ell) (Spec.map (CommRingCat.ofHom sigma.toRingHom)))).hom.app
            (((ProEtale.upperStar Ab.{u + 1} (Spec.map (CommRingCat.ofHom sigma.toRingHom))).mapMod
              (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell)
                (Spec (.of k)))).obj M)))).hom.toAddMonoidHom =
      ((ProEtale.geometricFieldEvaluationComparison
        (Spec.map (CommRingCat.ofHom sigma.toRingHom)) Ab.{u + 1}).app M.X).hom

/-- The open exchange is fixed by its mate under the actual open adjunction.
Source: the node's proof, step 6; the mate equality includes its unit/counit normalization
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
structure OpenTransport (ell : ℕ) [Fact ell.Prime]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i]
    (gx : X ⟶ X) (gz : Z ⟶ Z) (h : gx ≫ i = i ≫ gz) where
  exchange : extension ell i ⋙ pull ell gz ≅ pull ell gx ⋙ extension ell i
  normalization : Adjunction.squareExchange (openAdj ell i) (openAdj ell i)
    (pull ell gx) (pull ell gz) exchange.symm = (pullSquare ell h).inv

/-- The compact-support transport is point transport, the proper mate, then open exchange.
Source: the node's proof, steps 6--7
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def compactTransport {ell : ℕ} [Fact ell.Prime]
    {k : Type u} [Field k] [IsAlgClosed k] {sigma : k ≃+* k}
    (t : PointTransport ell k sigma) {X : Scheme.{u}}
    {a : X ⟶ Spec (.of k)} (c : Compactification a)
    (gx : X ⟶ X) (gz : c.Z ⟶ c.Z)
    (hg : gz ≫ c.g = c.g ≫ Spec.map (CommRingCat.ofHom sigma.toRingHom))
    {hi : gx ≫ c.i = c.i ≫ gz} (e : OpenTransport ell c.i gx gz hi) :
    condensedQbarCompactSections ell k c ⟶ pull ell gx ⋙ condensedQbarCompactSections ell k c :=
  Functor.whiskerLeft (extension ell c.i ⋙ push ell c.g) t.derived.hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (extension ell c.i)
        (properExchange ell c.g gz (Spec.map (CommRingCat.ofHom sigma.toRingHom)) hg))
          (condensedQbarDerivedPointSections ell k) ≫
    Functor.whiskerRight (Functor.whiskerRight e.exchange.hom (push ell c.g))
      (condensedQbarDerivedPointSections ell k)

/-- Geometric Frobenius on compact cohomology is induced by the specified Weil isomorphism.
Source: the node's displayed definition of F_X and its proof, step 7
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def action {ell : ℕ} [Fact ell.Prime] {k : Type u} [Field k] [IsAlgClosed k]
    {sigma : k ≃+* k} (t : PointTransport ell k sigma) {X : Scheme.{u}}
    {a : X ⟶ Spec (.of k)} (c : Compactification a)
    (gx : X ⟶ X) (gz : c.Z ⟶ c.Z)
    (hg : gz ≫ c.g = c.g ≫ Spec.map (CommRingCat.ofHom sigma.toRingHom))
    {hi : gx ≫ c.i = c.i ≫ gz} (e : OpenTransport ell c.i gx gz hi)
    (K : DMod ell X) (theta : (pull ell gx).obj K ≅ K) :
    End ((condensedQbarCompactSections ell k c).obj K) :=
  (compactTransport t c gx gz hg e).app K ≫ (condensedQbarCompactSections ell k c).map theta.hom

/-- The fixed geometric field automorphism used by the recorded scheme Frobenius.
Source: def-weil-frobenius-detailed, geometric Frobenius convention
(blueprint: lem-zl-condensed-clopen-compact-decomposition). -/
def fieldFrobenius (D : FiniteFieldDatum.{u}) : D.k ≃+* D.k := by
  letI := Fintype.ofFinite D.k₀
  exact (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv

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

namespace WeilConjectures.CondensedClopenCompact

private theorem compactification_frobenius_comm (D : FiniteFieldDatum.{u})
    (X : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom) :
    (D.geometricFrobenius X).hom ≫ (geometricCompactification D c).i =
      (geometricCompactification D c).i ≫ compactificationFrobenius D c := by
  let σ := @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
    (Fintype.ofFinite D.k₀) _ _ _
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  change D.galoisMap X.hom σ ≫ (c.baseChange b).i =
    (c.baseChange b).i ≫ D.galoisMap c.g σ
  apply pullback.hom_ext
  · simp only [Category.assoc, Compactification.baseChange_i_fst]
    rw [← Category.assoc, (D.galoisMap_projections X.hom σ).1,
      (D.galoisMap_projections c.g σ).1]
    exact (c.baseChange_i_fst b).symm
  · simp only [Category.assoc, Compactification.baseChange_i_snd]
    rw [(D.galoisMap_projections X.hom σ).2,
      (D.galoisMap_projections c.g σ).2]
    simpa only [← Category.assoc] using congrArg
      (fun f ↦ f ≫ Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom))
      (c.baseChange_i_snd b).symm

private theorem component_frobenius_comm (D : FiniteFieldDatum.{u})
    {U X : Over (Spec (.of D.k₀))} (j : U ⟶ X)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (schemeFrobenius D U) ≫ geometricInclusion D j =
      geometricInclusion D j ≫ (D.geometricFrobenius X).hom := by
  let σ := @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
    (Fintype.ofFinite D.k₀) _ _ _
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  change D.galoisMap U.hom σ ≫ ((Over.pullback b).map j).left =
    ((Over.pullback b).map j).left ≫ D.galoisMap X.hom σ
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc, (D.galoisMap_projections U.hom σ).1,
      (D.galoisMap_projections X.hom σ).1]
    simp only [b, pullback.lift_fst]
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd]
    rw [(D.galoisMap_projections U.hom σ).2,
      (D.galoisMap_projections X.hom σ).2]
    simp only [← Category.assoc, b, pullback.lift_snd]

private theorem empty_geometric_fiber (D : FiniteFieldDatum.{u}) (X : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (I : Type w) [IsEmpty I] (U : I → Over (Spec (.of D.k₀))) (j : ∀ i, U i ⟶ X)
    (hcover : (⋃ i, Set.range (j i).left) = Set.univ) :
    IsEmpty (D.geometricFiber X).left := by
  refine ⟨fun x ↦ ?_⟩
  have hx : (pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) x ∈
      ⋃ i, Set.range (j i).left := by rw [hcover]; trivial
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
  exact isEmptyElim i

private theorem geometric_inclusion_range (D : FiniteFieldDatum.{u})
    {U X : Over (Spec (.of D.k₀))} (j : U ⟶ X) :
    Set.range (geometricInclusion D j) =
      (pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ⁻¹' Set.range j.left := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have h := Scheme.Pullback.range_map (f := U.hom) (g := b) X.hom b
    j.left (𝟙 _) (𝟙 _) (by simp) (by simp)
  simpa [b, geometricInclusion, Over.pullback_map_left, pullback.map] using h

private theorem restriction_bounded (ell : ℕ) [Fact ell.Prime] {U X : Scheme.{u}} (j : U ⟶ X)
    (K : ProEtale.BoundedConstructible
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell) X)) :
    ProEtale.boundedConstructible
      (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell) U)
      ((pull ell j).obj K.obj) := by
  have h := ProEtale.CondensedRing.boundedConstructible_leftDerivedUpperStar_obj_of_scheme
    (Profinite.padicAlgClRingObj ell) j K.obj K.property
  exact (ProEtale.boundedConstructible _).prop_of_iso
    ((ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.padicAlgClRingObj ell) j).app K.obj) h

private theorem galoisMap_isIso (D : FiniteFieldDatum.{u}) {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of D.k₀)) (sigma : D.k ≃ₐ[D.k₀] D.k) :
    IsIso (D.galoisMap f sigma) := by
  let e : _ ≅ _ := ⟨D.galoisMap f sigma, D.galoisMap f sigma.symm,
    (D.galoisMap_inverse f sigma).1, (D.galoisMap_inverse f sigma).2⟩
  exact e.isIso_hom

private theorem isIso_desc_of_bicone
    {C : Type*} [Category* C] [Preadditive C]
    {I : Type w} [Fintype I] [DecidableEq I] (F : I → C) [HasBiproduct F]
    {G : C} (inc : ∀ i, F i ⟶ G) (pr : ∀ i, G ⟶ F i)
    (hd : ∀ i k, inc i ≫ pr k =
      if h : i = k then eqToHom (congrArg F h) else 0)
    (hs : ∑ i, pr i ≫ inc i = 𝟙 G) : IsIso (biproduct.desc inc) := by
  let b : Bicone F :=
    { pt := G
      π := pr
      ι := inc
      ι_π := by
        intro i k
        by_cases h : i = k <;> simpa [h] using hd i k }
  exact (biproduct.uniqueUpToIso F (isBilimitOfTotal b hs)).isIso_inv

private theorem component_action_compat
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (G : C ⥤ C) (H : B ⥤ B) (J : C ⥤ B) (F : C ⥤ E) (Fi : B ⥤ E)
    (s : G ⋙ J ≅ J ⋙ H) (inc : J ⋙ Fi ⟶ F)
    (ct : F ⟶ G ⋙ F) (cti : Fi ⟶ H ⋙ Fi)
    (ht : inc ≫ ct = Functor.whiskerLeft J cti ≫
      Functor.whiskerRight s.inv Fi ≫ Functor.whiskerLeft G inc)
    (K : C) (theta : G.obj K ⟶ K) :
    inc.app K ≫ (ct.app K ≫ F.map theta) =
      (cti.app (J.obj K) ≫ Fi.map (s.inv.app K ≫ J.map theta)) ≫
        inc.app K := by
  have h := congrArg (fun a ↦ a.app K) ht
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rw [← inc.naturality theta]
  rfl

end WeilConjectures.CondensedClopenCompact
