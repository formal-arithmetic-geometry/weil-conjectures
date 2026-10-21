/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.CategoryTheory.CondensedProductActionInflation
public import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.AllContinuousScalarMate
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Sheaf.Paper.NormContinuousMonodromyData
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.RootTowerLisseMorphismExtension

/-! # Partial Kummer boundary model of the closed unit

Source: blueprint main-20261015, direct-image stability proof, paragraph (3),
agent-formulated two-stage Kummer calculation, exact geometric reference WANTED.
(blueprint: lem-sfb-partial-kummer-boundary-unit-model).

The comparison below lives in the unbounded derived category and specifies the arrow.
The two coefficient fields use all continuous functions and the same finite-dimensional
E-representation. Inflation adjunctions are normalized on profinite sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PartialKummer
open Profinite.CondensedAction

/-- Internal modules over the coefficient pulled back from the point.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
abbrev SchemeModules
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R]
    (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)

/-- The group of prime-to-p inertia coordinates indexed by a subset of the branches.
The lift only places the existing product of q-adic integers in the site universe.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
abbrev Inertia (p : ℕ) {n : ℕ} (J : Finset (Fin n)) :=
  {a : Fin n // a ∈ J} → ULift.{u} (Multiplicative
    (∀ q : {q : Nat.Primes // (q : ℕ) ≠ p}, @PadicInt q.val (Fact.mk q.val.property)))

/-- A finite-dimensional norm-topological E-representation, written in a finite basis.
The coordinate space has its product norm topology; dimension zero is included.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
structure FiniteRepresentation (E : Type) [NormedField E]
    (G : Type u) [Group G] [TopologicalSpace G] where
  representation : NormContinuousRepresentations E G
  rank : ℕ
  basis : Module.Basis (Fin rank) E representation.obj.V

/-- The existing continuous representation expressed in the chosen finite basis.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def FiniteRepresentation.action {E : Type} [NormedField E]
    {G : Type u} [Group G] [TopologicalSpace G]
    (M : FiniteRepresentation E G) (g : G) (x : Fin M.rank → E) : Fin M.rank → E :=
  M.basis.equivFun (M.representation.obj.ρ g (M.basis.equivFun.symm x))

/-- The canonical diagonal morphism C(-,F) -> C(-,F^d).
Source: finite-basis description in direct-image proof (3)
(blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def diagonal (F : Type) [TopologicalSpace F] [CommRing F] [IsTopologicalRing F] (d : ℕ) :
    Profinite.continuousMapRingObj.{u} F ⟶
      Profinite.continuousMapRingObj (Fin d → F) :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (RingHom.pi (fun _ : Fin d ↦ RingHom.id F)) (continuous_pi fun _ ↦ continuous_id))

/-- The diagonal preserves the pointwise ring-object operations.
Source: finite-basis description in direct-image proof (3)
(blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
instance diagonal_isMonHom (F : Type) [TopologicalSpace F] [CommRing F]
    [IsTopologicalRing F] (d : ℕ) : IsMonHom (diagonal.{u} F d) :=
  Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafMap
      (RingHom.pi (fun _ : Fin d ↦ RingHom.id F)) (continuous_pi fun _ ↦ continuous_id))

/-- The actual condensed F-module S -> C(S,F^d), with pointwise scalar multiplication.
Source: M_(alpha,F) in direct-image proof (3)
(blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def coordinateModule (F : Type) [TopologicalSpace F] [CommRing F] [IsTopologicalRing F]
    (d : ℕ) : Modules (Mon.mk (Profinite.continuousMapRingObj.{u} F)) :=
  (Mod.comap (diagonal F d)).obj (Mod.regular (Profinite.continuousMapRingObj (Fin d → F)))

/-- A presentation of the condensed scalar extension of a finite E-representation.
The pointwise equation specifies the action on every profinite family, including after
restriction. Scalar extension uses F^d, the finite-basis description of F tensor_E M.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
structure Condensation {E : Type} [NormedField E] {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (M : FiniteRepresentation E G)
    (F : Type) [NormedField F] (ι : E →+* F) where
  object : ActionModule (Mon.mk (Profinite.continuousMapRingObj.{u} F)) G
  coordinates : object.module ≅ coordinateModule F M.rank
  action_coordinates : ∀ (S : Profinite.{u}) (g : C(S, G))
    (x : sectionModule (Mon.mk (Profinite.continuousMapRingObj F)) object.module S)
    (s : S) (i : Fin M.rank),
    (ULift.down ((coordinates.hom.hom.hom.app (op S)).hom (object.act S g x)) s) i =
      ∑ j : Fin M.rank, ι (M.action (g s) (Pi.single j 1) i) *
        (ULift.down ((coordinates.hom.hom.hom.app (op S)).hom x) s) j

section Geometry
variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]
variable {Y V W Z : Scheme.{u}} (b : W ⟶ V) (j : V ⟶ Y) (h : Z ⟶ V)

/-- The actual closed inverse-image/direct-image unit on Rb_*L[0]. The direct image of
a closed immersion is exact, so its total right derived functor is canonically its
termwise functor. This formula uses the actual derived adjunction, not a chosen arrow.
Source: direct-image proof (3), u_F
(blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def unitArrow (L : SchemeModules R W) :
    (CondensedRing.moduleObjectDerivedPushforward R j).obj
        ((CondensedRing.moduleObjectDerivedPushforward R b).obj
          ((DerivedCategory.singleFunctor _ 0).obj L)) ⟶
      (CondensedRing.moduleObjectDerivedPushforward R j).obj
        ((CondensedRing.moduleObjectDerivedPushforward R h).obj
          ((CondensedRing.upperStar R h).mapDerivedCategory.obj
            ((CondensedRing.moduleObjectDerivedPushforward R b).obj
              ((DerivedCategory.singleFunctor _ 0).obj L)))) :=
  (CondensedRing.moduleObjectDerivedPushforward R j).map
    ((CondensedRing.upperStarLowerStarAdjunction R h).mapDerivedCategoryRightDerivedAdjunction
      |>.unit.app _)
end Geometry

/-- The abelian structure of an action category with its fixed sectionwise addition.
Only the proof fields and limit existence fields are packaged; no addition is chosen.
Source: product action inflation (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
class ActionAbelianData (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop where
  normalMono : IsNormalMonoCategory (ActionModule R G)
  normalEpi : IsNormalEpiCategory (ActionModule R G)
  products : HasFiniteProducts (ActionModule R G)
  kernels : HasKernels (ActionModule R G)
  cokernels : HasCokernels (ActionModule R G)

/-- Assemble the existing abelian structure without changing the native addition.
Source: product action inflation (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
instance actionAbelian (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [a : ActionAbelianData R G] : Abelian (ActionModule R G) where
  toPreadditive := actionPreadditive
  toIsNormalMonoCategory := a.normalMono
  toIsNormalEpiCategory := a.normalEpi
  has_finite_products := a.products
  has_kernels := a.kernels
  has_cokernels := a.cokernels

section Invariants
variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
  (G H : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [ActionAbelianData R G] [ActionAbelianData R (G × H)]
  [IsGrothendieckAbelian.{u + 1} (ActionModule R G)]
  [IsGrothendieckAbelian.{u + 1} (ActionModule R (G × H))]
  [HasDerivedCategory.{u + 2} (ActionModule R G)]
  [HasDerivedCategory.{u + 2} (ActionModule R (G × H))]
  [(trivial (R := R) (P := G)).Additive]
  [PreservesFiniteLimits (trivial (R := R) (P := G))]
  [PreservesFiniteColimits (trivial (R := R) (P := G))]
  [(trivial (R := R) (P := G × H)).Additive]
  [PreservesFiniteLimits (trivial (R := R) (P := G × H))]
  [PreservesFiniteColimits (trivial (R := R) (P := G × H))]
  [(inflate (R := R) (ContinuousMonoidHom.fst G H)).Additive]
  [PreservesFiniteLimits (inflate (R := R) (ContinuousMonoidHom.fst G H))]
  [PreservesFiniteColimits (inflate (R := R) (ContinuousMonoidHom.fst G H))]
  (dG : Invariants R G) (dGH : Invariants R (G × H)) (dHG : ProductInvariants R G H)
  [dG.functor.Additive] [dGH.functor.Additive] [dHG.functor.Additive]

/-- The canonical product-to-iterated derived-invariants comparison: conjugate the
composition of the exact inflation functors, using the specified invariants adjunctions.
The comparison of left adjoints is the identity on their actual modules and section maps.
Source: direct-image proof (3), theta
(blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def theta (e : trivial (R := R) (P := G) ⋙
      inflate (R := R) (ContinuousMonoidHom.fst G H) ≅ trivial (R := R) (P := G × H)) :
    dGH.functor.rightDerivedFunctor ≅
      dHG.functor.rightDerivedFunctor ⋙ dG.functor.rightDerivedFunctor :=
  conjugateIsoEquiv dGH.adjunction.mapDerivedCategoryRightDerivedAdjunction
    (dG.adjunction.mapDerivedCategoryRightDerivedAdjunction.comp
      dHG.adjunction.mapDerivedCategoryRightDerivedAdjunction)
    (Adjunction.derivedCompositionLeftIso _ _ _ e)
end Invariants

/-- The normalized invariant adjunctions with the proof-only structures needed to
apply ordinary K-injective right derivation. Their existence is part of the recorded
product-action theorem, rather than a hypothesis on geometric input.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
class DerivedInvariants (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    (G H : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] where
  [outerAbelian : ActionAbelianData R G]
  [productAbelian : ActionAbelianData R (G × H)]
  [outerGrothendieck : IsGrothendieckAbelian.{u + 1} (ActionModule R G)]
  [productGrothendieck : IsGrothendieckAbelian.{u + 1} (ActionModule R (G × H))]
  [outerDerived : HasDerivedCategory.{u + 2} (ActionModule R G)]
  [productDerived : HasDerivedCategory.{u + 2} (ActionModule R (G × H))]
  [outerTrivialAdditive : (trivial (R := R) (P := G)).Additive]
  [outerTrivialLeft : PreservesFiniteLimits (trivial (R := R) (P := G))]
  [outerTrivialRight : PreservesFiniteColimits (trivial (R := R) (P := G))]
  [productTrivialAdditive : (trivial (R := R) (P := G × H)).Additive]
  [productTrivialLeft : PreservesFiniteLimits (trivial (R := R) (P := G × H))]
  [productTrivialRight : PreservesFiniteColimits (trivial (R := R) (P := G × H))]
  [inflateAdditive : (inflate (R := R) (ContinuousMonoidHom.fst G H)).Additive]
  [inflateLeft : PreservesFiniteLimits (inflate (R := R) (ContinuousMonoidHom.fst G H))]
  [inflateRight : PreservesFiniteColimits (inflate (R := R) (ContinuousMonoidHom.fst G H))]
  outer : Invariants R G
  product : Invariants R (G × H)
  inner : ProductInvariants R G H
  [outerAdditive : outer.functor.Additive]
  [productAdditive : product.functor.Additive]
  [innerAdditive : inner.functor.Additive]
  inflation_eq : trivial (R := R) (P := G × H) =
    trivial (R := R) (P := G) ⋙ inflate (R := R) (ContinuousMonoidHom.fst G H)

attribute [instance] DerivedInvariants.outerAbelian DerivedInvariants.productAbelian
  DerivedInvariants.outerGrothendieck DerivedInvariants.productGrothendieck
  DerivedInvariants.outerTrivialAdditive DerivedInvariants.outerTrivialLeft
  DerivedInvariants.outerTrivialRight DerivedInvariants.productTrivialAdditive
  DerivedInvariants.productTrivialLeft DerivedInvariants.productTrivialRight
  DerivedInvariants.inflateAdditive DerivedInvariants.inflateLeft DerivedInvariants.inflateRight
  DerivedInvariants.outerAdditive DerivedInvariants.productAdditive DerivedInvariants.innerAdditive

attribute [instance_reducible] DerivedInvariants.outerDerived DerivedInvariants.productDerived
attribute [instance] DerivedInvariants.outerDerived DerivedInvariants.productDerived

/-- The prescribed comparison on an action module in degree zero.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def DerivedInvariants.comparison {R : Profinite.CondensedRing.{u}} [IsCommMonObj R.X]
    {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [d : DerivedInvariants R G H] (M : ActionModule R (G × H)) :=
  (theta R G H d.outer d.product d.inner (eqToIso d.inflation_eq.symm)).hom.app
    ((DerivedCategory.singleFunctor _ 0).obj M)

/-- Pullback of internal modules from the condensed point; its coefficient ring is
literally the previously recorded pulled-back ring object.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
abbrev pointPull (R : Profinite.CondensedRing.{u}) (T : Scheme.{u}) :
    Modules R ⥤ SchemeModules R.X T := (upperStarFromPoint T).mapMod R.X

/-- Exactness of the recorded inverse image on internal modules.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
instance pointPull_finiteLimits (R : Profinite.CondensedRing.{u}) (T : Scheme.{u}) :
    PreservesFiniteLimits (pointPull R T) :=
  inferInstanceAs (PreservesFiniteLimits
    ((Functor.sheafPullbackConstruction.sheafPullback profiniteToProEt Ab.{u + 1}
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ) ⋙
        (toSpecZ T)^*[Ab.{u + 1}]).mapMod R.X))

/-- Colimit preservation of the recorded inverse image on internal modules.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
instance pointPull_finiteColimits (R : Profinite.CondensedRing.{u}) (T : Scheme.{u}) :
    PreservesFiniteColimits (pointPull R T) :=
  letI : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
  letI : PreservesFiniteColimits (upperStarFromPoint T) :=
    comp_preservesFiniteColimits pointUpperStar ((toSpecZ T)^*[Ab.{u + 1}])
  inferInstanceAs (PreservesFiniteColimits ((upperStarFromPoint T).mapMod R.X))

/-- Point pullback is additive, as is its underlying exact inverse image.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
instance pointPull_additive (R : Profinite.CondensedRing.{u}) (T : Scheme.{u}) :
    (pointPull R T).Additive :=
  Functor.additive_of_preserves_binary_products (pointPull R T)

/-- The source of the restricted closed-unit arrow, functorial in L.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def sourceFunctor (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    {Y V W T : Scheme.{u}} (b : W ⟶ V) (j : V ⟶ Y) (t : T ⟶ Y) :=
  DerivedCategory.singleFunctor (SchemeModules R.X W) 0 ⋙
    CondensedRing.moduleObjectDerivedPushforward R.X b ⋙
    CondensedRing.moduleObjectDerivedPushforward R.X j ⋙
    (CondensedRing.upperStar R.X t).mapDerivedCategory

/-- The target of the restricted closed-unit arrow, functorial in L.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def targetFunctor (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    {Y V W Z T : Scheme.{u}} (b : W ⟶ V) (j : V ⟶ Y) (h : Z ⟶ V) (t : T ⟶ Y) :=
  DerivedCategory.singleFunctor (SchemeModules R.X W) 0 ⋙
    CondensedRing.moduleObjectDerivedPushforward R.X b ⋙
    (CondensedRing.upperStar R.X h).mapDerivedCategory ⋙
    CondensedRing.moduleObjectDerivedPushforward R.X h ⋙
    CondensedRing.moduleObjectDerivedPushforward R.X j ⋙
    (CondensedRing.upperStar R.X t).mapDerivedCategory

/-- A comparison on an entire chart, identifying both derived objects and the actual
closed-unit arrow with the normalized product-to-iterated comparison. Pullback of this
square gives the comparison on every restriction of the chart.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
structure LocalModel
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    {Y V W Z T : Scheme.{u}} (b : W ⟶ V) (j : V ⟶ Y) (h : Z ⟶ V) (t : T ⟶ Y)
    (L : SchemeModules R.X W)
    {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [d : DerivedInvariants R G H] (M : ActionModule R (G × H)) where
  sourceIso : (CondensedRing.upperStar R.X t).mapDerivedCategory.obj
      ((CondensedRing.moduleObjectDerivedPushforward R.X j).obj
        ((CondensedRing.moduleObjectDerivedPushforward R.X b).obj
          ((DerivedCategory.singleFunctor _ 0).obj L))) ≅
    (pointPull R T).mapDerivedCategory.obj
      (d.product.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj M))
  targetIso : (CondensedRing.upperStar R.X t).mapDerivedCategory.obj
      ((CondensedRing.moduleObjectDerivedPushforward R.X j).obj
        ((CondensedRing.moduleObjectDerivedPushforward R.X h).obj
          ((CondensedRing.upperStar R.X h).mapDerivedCategory.obj
            ((CondensedRing.moduleObjectDerivedPushforward R.X b).obj
              ((DerivedCategory.singleFunctor _ 0).obj L))))) ≅
    (pointPull R T).mapDerivedCategory.obj
      (d.outer.functor.rightDerivedFunctor.obj
        (d.inner.functor.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj M)))
  unit_eq : (CondensedRing.upperStar R.X t).mapDerivedCategory.map
      (unitArrow R.X b j h L) ≫ targetIso.hom =
    sourceIso.hom ≫ (pointPull R T).mapDerivedCategory.map (d.comparison M)

/-- The component family of the SNC witness, with no second definition of components.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
abbrev components {Y : Scheme.{u}} (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D) := hD.2.2.choose_spec.choose

/-- The locally closed stratum where exactly the components indexed by J occur.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def stratumSet {Y : Scheme.{u}} (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D) (J : Finset (Fin hD.2.2.choose)) : Set Y :=
  {y | ∀ a, y ∈ (components D hD a).support ↔ a ∈ J}

/-- A common covering chart has compatible primitive roots of every prime-to-p order.
They are sections on the chart, so the choices persist under every further restriction.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def CompatibleRoots (p : ℕ) (T : Scheme.{u}) : Prop :=
  ∃ ζ : TameRootOrder p → Γ(T, ⊤)ˣ,
    (∀ n, IsPrimitiveRoot (ζ n) n.val) ∧
    ∀ n m, n.val ∣ m.val → ζ m ^ (m.val / n.val) = ζ n

/-- Simultaneous models for E and its norm-topological algebraic closure, using one
finite-dimensional E-representation and the same roots of unity and chart.
Source: direct-image proof (3) (blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
structure ChartModel
    (p ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {Y V W Z T : Scheme.{u}} (b : W ⟶ V) (j : V ⟶ Y) (h : Z ⟶ V) (t : T ⟶ Y)
    (L : SchemeModules (Profinite.continuousMapRingObj E.1) W)
    {n : ℕ} (Jo Ji : Finset (Fin n)) where
  roots : CompatibleRoots p T
  [invariantsE : DerivedInvariants (Mon.mk (Profinite.continuousMapRingObj E.1))
    (Inertia.{u} p Jo) (Inertia.{u} p Ji)]
  [invariantsOmega :
    DerivedInvariants (Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ)))
      (Inertia.{u} p Jo) (Inertia.{u} p Ji)]
  representation : FiniteRepresentation E.1 (Inertia.{u} p Jo × Inertia.{u} p Ji)
  condensedE : Condensation representation E.1 (RingHom.id E.1)
  condensedOmega : Condensation representation (PadicAlgCl ℓ) E.1.subtype
  modelE : LocalModel (Mon.mk (Profinite.continuousMapRingObj E.1))
    b j h t L condensedE.object
  modelOmega : LocalModel (Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ)))
    b j h t ((Mod.extendScalars
      (coefficientMap (CondensedRing.tameBoundaryScalarMap ℓ E) W)).obj L)
    condensedOmega.object

/-- A linear E-map and its scalar-extended condensed map have the same matrix on
all profinite families. This specifies the map rather than choosing an unrelated one.
Source: naturality in L, direct-image proof (3)
(blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def HasMatrix {E : Type} [NormedField E] {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {M N : FiniteRepresentation E G}
    {F : Type} [NormedField F] {ι : E →+* F}
    (CM : Condensation.{u} M F ι) (CN : Condensation.{u} N F ι)
    (a : (Fin M.rank → E) →ₗ[E] (Fin N.rank → E)) (f : CM.object ⟶ CN.object) : Prop :=
  ∀ (S : Profinite.{u})
    (x : sectionModule (Mon.mk (Profinite.continuousMapRingObj F)) CM.object.module S)
    (s : S) (i : Fin N.rank),
    (ULift.down ((CN.coordinates.hom.hom.hom.app (op S)).hom
      ((f.val.hom.hom.app (op S)).hom x)) s) i =
      ∑ j : Fin M.rank, ι (a (Pi.single j 1) i) *
        (ULift.down ((CM.coordinates.hom.hom.hom.app (op S)).hom x) s) j

/-- Naturality of both object identifications for an actual coefficient-module map.
Pulling back these equations along any morphism of charts is refinement compatibility.
Source: naturality in L and covering restriction, direct-image proof (3)
(blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def ModelNatural
    (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    {Y V W Z T : Scheme.{u}} {b : W ⟶ V} {j : V ⟶ Y} {h : Z ⟶ V} {t : T ⟶ Y}
    {L L' : SchemeModules R.X W} (f : L ⟶ L')
    {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [d : DerivedInvariants R G H] {M M' : ActionModule R (G × H)}
    (m : M ⟶ M') (c : LocalModel R b j h t L M) (c' : LocalModel R b j h t L' M') : Prop :=
  (sourceFunctor R b j t).map f ≫ c'.sourceIso.hom =
    c.sourceIso.hom ≫ (pointPull R T).mapDerivedCategory.map
      (d.product.functor.rightDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map m)) ∧
  (targetFunctor R b j h t).map f ≫ c'.targetIso.hom =
    c.targetIso.hom ≫ (pointPull R T).mapDerivedCategory.map
      (d.outer.functor.rightDerivedFunctor.map
        (d.inner.functor.rightDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map m)))

/-- The actual matrix maps intertwine the local models for both coefficient rings.
The invariant functors in the two chart models agree, so the naturality equations
compare morphisms in precisely the same derived categories.
Source: naturality in L, direct-image proof (3)
(blueprint: lem-sfb-partial-kummer-boundary-unit-model). -/
def ChartModelsNatural
    {p ℓ : ℕ} [Fact ℓ.Prime] {E : PadicAlgCl.FiniteIntermediateField ℓ}
    {Y V W Z T : Scheme.{u}} {b : W ⟶ V} {j : V ⟶ Y} {h : Z ⟶ V} {t : T ⟶ Y}
    {L L' : SchemeModules (Profinite.continuousMapRingObj E.1) W} (f : L ⟶ L')
    {n : ℕ} {Jo Ji : Finset (Fin n)}
    (C : ChartModel p ℓ E b j h t L Jo Ji)
    (C' : ChartModel p ℓ E b j h t L' Jo Ji) : Prop :=
  ∃ (eE : C.invariantsE = C'.invariantsE)
    (eΩ : C.invariantsOmega = C'.invariantsOmega)
    (a : (Fin C.representation.rank → E.1) →ₗ[E.1] (Fin C'.representation.rank → E.1))
    (mE : C.condensedE.object ⟶ C'.condensedE.object)
    (mΩ : C.condensedOmega.object ⟶ C'.condensedOmega.object),
    (∀ g x, a (C.representation.action g x) = C'.representation.action g (a x)) ∧
    HasMatrix C.condensedE C'.condensedE a mE ∧
    HasMatrix C.condensedOmega C'.condensedOmega a mΩ ∧
    ModelNatural (d := C.invariantsE)
      (Mon.mk (Profinite.continuousMapRingObj E.1)) f mE
      C.modelE (eE.symm ▸ C'.modelE) ∧
    ModelNatural (d := C.invariantsOmega)
      (Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ)))
      ((Mod.extendScalars (coefficientMap (CondensedRing.tameBoundaryScalarMap ℓ E) W)).map f)
      mΩ C.modelOmega (eΩ.symm ▸ C'.modelOmega)

/-- The partial Kummer model of the actual closed unit, on a covering of the entire
stratum, simultaneously for the two all-continuous coefficient rings.
Source: blueprint main-20261015, direct-image proof paragraph (3), geometric two-stage
Kummer-nerve calculation, exact geometric reference WANTED
(blueprint: lem-sfb-partial-kummer-boundary-unit-model).

Proof, following all seven DAG steps:
1. lem-sfb-tame-root-tower-extension supplies charts of the whole stratum, compatible
roots and an equivariant lisse extension on the full root tower. Restriction to the
boundary gives M. Tensoring finite free trivializations gives the same charts for Omega.
2. lem-weil-proetale-weakly-etale-localization and lem-sfb-derived-cech-image-totalization
express the restricted source by the coherent nonnegative Cech resolution. For every
profinite nerve parameter P, lem-sfb-root-tower-boundary-acyclicity identifies its term
with the derived internal Hom from C_F[P]. The action face and all other faces agree;
lem-sfb-condensed-derived-invariant-bar identifies the totalization with product invariants.
3. lem-weil-pbc-proetale-ringed-open-closed and
lem-sfb-cech-localization-unit-totalization carry the actual closed unit through the
same descent. All resolution degrees are nonnegative; no unbounded product interchange
or preservation of injectives by closed inverse image is asserted.
4. lem-sfb-root-tower-inner-support identifies the termwise closed-unit map on the base
V (whose closed complement is the union of the inner branches). Its equation with the
boundary-acyclicity comparison holds for every profinite family, hence cosimplicially.
5. Adjoining inner roots and then outer roots gives the same algebra as adjoining both.
The two deck actions commute. lem-sfb-condensed-product-bar-comparison identifies the
target with iterated invariants. Its augmentation normalization gives exactly theta.
6. lem-sfb-condensed-product-action-inflation and
lem-sfb-derived-composition-adjunction-normalization give the K-injective normalization.
lem-sfb-root-tower-lisse-morphism-extension extends actual puncture morphisms uniquely;
uniqueness gives equivariance on all profinite families, and hence naturality. Restricting
these squares gives refinement compatibility. Scalar extension is never moved past Rj_*.
7. The empty stratum has the empty cover. Empty Jo gives the trivial outer group;
nonempty Ji excludes an empty inner support. Dimension zero gives zero throughout.
-/
theorem partial_kummer_boundary_unit_model
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (_hY : IsRegularScheme Y)
    (D : Y.IdealSheafData) (hD : IsStrictNormalCrossingsBoundary D)
    (out J : Finset (Fin hD.2.2.choose)) (_hJi : (J \ out).Nonempty)
    (W V Z S : Scheme.{u})
    (b : W ⟶ V) (j : V ⟶ Y) (h : Z ⟶ V) (s : S ⟶ Y)
    [IsOpenImmersion b] [IsOpenImmersion j] [IsClosedImmersion h] [IsReduced Z]
    [IsImmersion s] [IsReduced S]
    (_hW : Set.range (b ≫ j) = (D.support : Set Y)ᶜ)
    (_hV : Set.range j =
      (⋃ a ∈ out, ((components D hD a).support : Set Y))ᶜ)
    (_hZ : Set.range h = (Set.range b)ᶜ)
    (_hS : Set.range s = stratumSet D hD J)
    (L : SchemeModules (Profinite.continuousMapRingObj E.1) W)
    (_hL : IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) L)
    (_htame : IsStrictLocalKummerTameModule p (Profinite.continuousMapRingObj E.1)
      D (b ≫ j) L) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
      (∀ a : U.I₀, Nonempty
        (ChartModel p ℓ E b j h (U.f a ≫ s) L (J ∩ out) (J \ out))) ∧
      ∀ (L' : SchemeModules (Profinite.continuousMapRingObj E.1) W),
        IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) L' →
        IsStrictLocalKummerTameModule p (Profinite.continuousMapRingObj E.1)
          D (b ≫ j) L' →
        ∀ f : L ⟶ L', ∃ U' : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
          ∀ a : U'.I₀, ∃ (C : ChartModel p ℓ E b j h (U'.f a ≫ s) L (J ∩ out) (J \ out))
            (C' : ChartModel p ℓ E b j h (U'.f a ≫ s) L' (J ∩ out) (J \ out)),
            ChartModelsNatural f C C' := by
  sorry

end AlgebraicGeometry.ProEtale.PartialKummer

