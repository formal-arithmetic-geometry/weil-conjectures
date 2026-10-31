/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldActionToposCoefficients
public import WeilConjectures.CategoryTheory.CondensedActionModule
public import WeilConjectures.CategoryTheory.CondensedEquivariantBarData
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.RingedPresentationTransport
import WeilConjectures.CategoryTheory.SectionRingLaxPushforwardCoherence
import WeilConjectures.AlgebraicGeometry.RelativeProfiniteTestLabels
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.SheafActionGrothendieckInflation
import WeilConjectures.CategoryTheory.SheafProductFixedAdjunction
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement

/-! # Normalized field-module equivalence and geometric section adjunction

Source: current blueprint, six-functors direct-images proof paragraph (3),
agent structural input; Bhatt--Scholze, Examples 4.1.9--4.1.10; Stacks Tags 03D6,
03D7 and 08BJ (blueprint: lem-sfb-geometric-sections-adjunction).

The statement uses the upstream normalized free tests directly. In particular it
has no import of the downstream global-descent theorem or its helper declarations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction.CoherentPresentation
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GeometricSectionsAdjunction

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Forget an internal field module to its set sheaf, retaining its actual sections.
Source: Stacks 00YV (blueprint: lem-sfb-geometric-sections-adjunction). -/
abbrev fieldSets (R : CategoryTheory.CondensedBar.Ring.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X ⥤ FieldActionTopos.FieldSheaves k :=
  Mod.forget (coefficientRing (Spec (.of k)) R.toMon).X ⋙
    sheafCompose _ (forget Ab.{u + 1})

/-- Forget an action module to the recorded small-model condensed set sheaf.
Source: Bhatt--Scholze Example 4.1.10
(blueprint: lem-sfb-geometric-sections-adjunction). -/
abbrev actionSets (R : CategoryTheory.CondensedBar.Ring.{u}) :
    Profinite.CondensedAction.ActionModule R.toMon (Ω ≃ₐ[k] Ω) ⥤
      Sheaf baseCoverage.toGrothendieck (Type (u + 1)) :=
  Profinite.CondensedAction.forgetAction ⋙ Mod.forget R.X ⋙
    sheafCompose _ (forget Ab.{u + 1}) ⋙ FieldActionTopos.transport

/-- Forget the action in the fixed set-topos presentation.
Source: Bhatt--Scholze Example 4.1.10
(blueprint: lem-sfb-geometric-sections-adjunction). -/
def actionUnderlying : Actions (Ω ≃ₐ[k] Ω) ⥤
    Sheaf baseCoverage.toGrothendieck (Type (u + 1)) := by
  letI : MonoidalCategory (Sheaf baseCoverage.toGrothendieck (Type (u + 1))) :=
    ObjectProperty.fullMonoidalSubcategory _
  exact Mod.forget _

/-- Module transport over the specified set-topos equivalence. Sections are compared
on its original free tests, and the scalar map is the actual point-adjunction unit
followed by restriction along its cover. No downstream geometric-data interface is used.
Source: Bhatt--Scholze Examples 4.1.9--4.1.10; Stacks 03D7, 08BJ
(blueprint: lem-sfb-geometric-sections-adjunction). -/
structure NormalizedModules (h : FieldActionTopos.Normalization k Ω)
    (R : CategoryTheory.CondensedBar.Ring.{u})
    [CategoryTheory.CondensedBar.ActionAbelian R (Ω ≃ₐ[k] Ω)]
    [HasDerivedCategory.{u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (coefficientRing (Spec (.of k)) R.toMon).X)]
    [HasDerivedCategory.{u + 2}
      (Profinite.CondensedAction.ActionModule R.toMon (Ω ≃ₐ[k] Ω))] where
  /-- The module lift of the fixed equivalence. -/
  functor : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
    (coefficientRing (Spec (.of k)) R.toMon).X ⥤
      Profinite.CondensedAction.ActionModule R.toMon (Ω ≃ₐ[k] Ω)
  /-- Addition is the original addition on internal-module maps. -/
  [additive : functor.Additive]
  /-- The functor is an equivalence of the original categories. -/
  [equivalence : functor.IsEquivalence]
  /-- Exactness includes kernels. -/
  [limits : PreservesFiniteLimits functor]
  /-- Exactness includes cokernels. -/
  [colimits : PreservesFiniteColimits functor]
  /-- Its underlying set sheaf is the fixed E, not an unrelated equivalence. -/
  underlying : functor ⋙ actionSets k Ω R ≅
    fieldSets k R ⋙ h.equivalence.functor ⋙ actionUnderlying k Ω
  /-- The additive section identification on the original geometric free tests. -/
  sections (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X) (P : Base.{u}) :
    (functor.obj N).module.X.obj.obj (op (parameter P)) ≃+
      N.X.obj.obj (op ((Scheme.ProEt.qcqsInclusion _).obj (h.free.obj ⟨P⟩)))
  /-- This is precisely h's section identification. -/
  section_normalization (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X) (P : Base.{u})
      (m : (functor.obj N).module.X.obj.obj (op (parameter P))) :
    sections N P m = h.sections ((fieldSets k R).obj N) P
      (((underlying.hom.app N).hom.app (op P)) m)
  /-- The section comparison respects the original R(P)-action via the canonical
  coefficient map R(P) to R_s(bar s[P]), without changing the module structure. -/
  sections_smul (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X) (P : Base.{u})
      (r : CategoryTheory.CondensedBar.sectionRing R (parameter P))
      (m : Profinite.CondensedAction.sectionModule R.toMon (functor.obj N).module
        (parameter P)) :
    sections N P (r • m) =
      @SMul.smul
        ((InternalAbelianSheafModule.sectionRings _
          (condensedRingObj R.X (Spec (.of k)))).obj
            (op ((Scheme.ProEt.qcqsInclusion _).obj (h.free.obj ⟨P⟩))))
        (((InternalAbelianSheafModule.sectionModuleFunctor _
          (condensedRingObj R.X (Spec (.of k)))).obj N).val.obj
            (op ((Scheme.ProEt.qcqsInclusion _).obj (h.free.obj ⟨P⟩)))) _
        (((coefficientRing (Spec (.of k)) R.toMon).X.obj.map (h.cover P).op).hom
          ((((pointUpperStarLowerStarAdjunction.comp
            (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ (Spec (.of k))))).unit.app
              R.X).hom.app (op (parameter P))).hom r)) (sections N P m)
  /-- Every labeled arrow acts by b on f-star, in h's right-translation convention. -/
  restriction (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X) (P T : Base.{u}) (f : T ⟶ P)
      (b : (groupPresheaf (Ω ≃ₐ[k] Ω)).obj (op T))
      (m : Profinite.CondensedAction.sectionModule R.toMon (functor.obj N).module
        (parameter P)) :
    sections N T ((functor.obj N).act (parameter T) b.down
      (((functor.obj N).module.X.obj.map f.down.op).hom m)) =
        (N.X.obj.map ((Scheme.ProEt.qcqsInclusion _).map (h.free.map ⟨f, b⟩)).op).hom
          (sections N P m)
  /-- The underlying comparison intertwines every generalized action. -/
  underlying_action (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X) (P : Base.{u})
      (b : (groupPresheaf (Ω ≃ₐ[k] Ω)).obj (op P))
      (m : Profinite.CondensedAction.sectionModule R.toMon (functor.obj N).module
        (parameter P)) :
    ((underlying.hom.app N).hom.app (op P)) ((functor.obj N).act (parameter P) b.down m) =
      InternalActionSite.setAction baseCoverage (groupPresheaf (Ω ≃ₐ[k] Ω))
        (group_isSheaf (Ω ≃ₐ[k] Ω))
        (h.equivalence.functor.obj ((fieldSets k R).obj N)) (op P) b
          (((underlying.hom.app N).hom.app (op P)) m)
  /-- Ordinary unbounded localization of the termwise functor is an equivalence. -/
  derived : functor.mapDerivedCategory.IsEquivalence
  /-- Transport preserves K-injective complexes. -/
  kInjective : functor.PreservesKInjectiveComplexes
  /-- The inverse equivalence retains the original addition of maps. -/
  [inverseAdditive : functor.asEquivalence.inverse.Additive]
  /-- The inverse equivalence also preserves K-injectives. -/
  inverseKInjective : functor.asEquivalence.inverse.PreservesKInjectiveComplexes
  /-- The condensed module category is Grothendieck abelian. -/
  condensedGrothendieck : IsGrothendieckAbelian.{u + 1}
    (Profinite.CondensedAction.Modules R.toMon)
  /-- The field module category is Grothendieck abelian. -/
  fieldGrothendieck : IsGrothendieckAbelian.{u + 1}
    (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X)
  /-- The action category is Grothendieck abelian with its existing addition. -/
  actionGrothendieck : IsGrothendieckAbelian.{u + 1}
    (Profinite.CondensedAction.ActionModule R.toMon (Ω ≃ₐ[k] Ω))
  /-- The existing fixed-section specification includes both codomain transposes. -/
  invariants : Profinite.CondensedAction.Invariants R.toMon (Ω ≃ₐ[k] Ω)
  /-- Trivial inflation is additive. -/
  trivialAdditive : (Profinite.CondensedAction.trivial
    (R := R.toMon) (P := Ω ≃ₐ[k] Ω)).Additive
  /-- Trivial inflation preserves kernels. -/
  trivialLimits : PreservesFiniteLimits
    (Profinite.CondensedAction.trivial (R := R.toMon) (P := Ω ≃ₐ[k] Ω))
  /-- Trivial inflation preserves cokernels. -/
  trivialColimits : PreservesFiniteColimits
    (Profinite.CondensedAction.trivial (R := R.toMon) (P := Ω ≃ₐ[k] Ω))
  /-- The point inverse image becomes the actual trivial inflation. -/
  pointPull : (upperStarFromPoint (Spec (.of k))).mapMod R.X ⋙ functor ≅
    Profinite.CondensedAction.trivial (R := R.toMon) (P := Ω ≃ₐ[k] Ω)
  /-- The actual underlying point direct image, including all restrictions. -/
  pointUnderlying : functor ⋙ invariants.functor ⋙ Mod.forget R.X ≅
    Mod.forget (coefficientRing (Spec (.of k)) R.toMon).X ⋙
      (ProEtale.lowerStar Ab.{u + 1} (toSpecZ (Spec (.of k))) ⋙ pointLowerStar)
  /-- Module adjunction whose underlying unit and counit are the geometric ones below. -/
  pointAdjunction : (upperStarFromPoint (Spec (.of k))).mapMod R.X ⊣
    functor ⋙ invariants.functor
  /-- The underlying module unit is the actual point-adjunction unit. -/
  pointUnit (A : Profinite.CondensedAction.Modules R.toMon) :
    (pointAdjunction.unit.app A).hom ≫
        pointUnderlying.hom.app (((upperStarFromPoint (Spec (.of k))).mapMod R.X).obj A) =
      (pointUpperStarLowerStarAdjunction.comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ (Spec (.of k))))).unit.app A.X
  /-- The underlying module counit is the actual point-adjunction counit. -/
  pointCounit (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X) :
    (pointAdjunction.counit.app N).hom =
      (upperStarFromPoint (Spec (.of k))).map (pointUnderlying.hom.app N) ≫
        (pointUpperStarLowerStarAdjunction.comp
          (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ (Spec (.of k))))).counit.app N.X
  /-- The module comparison is the conjugate of the given inflation comparison. -/
  pointMate (A : Profinite.CondensedAction.Modules R.toMon)
      (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (coefficientRing (Spec (.of k)) R.toMon).X)
      (f : ((upperStarFromPoint (Spec (.of k))).mapMod R.X).obj A ⟶ N) :
    invariants.adjunction.homEquiv A (functor.obj N)
        (pointPull.inv.app A ≫ functor.map f) = pointAdjunction.homEquiv A N f
  /-- Included fixed sections are precisely restriction along h's geometric cover. -/
  pointRestriction (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X) (P : Base.{u})
      (m : Profinite.CondensedAction.sectionModule R.toMon
        (invariants.functor.obj (functor.obj N)) (parameter P)) :
    sections N P (((invariants.inclusion.app (functor.obj N)).hom.hom.app
      (op (parameter P))).hom m) =
        (N.X.obj.map (h.cover P).op).hom
          (((pointUnderlying.hom.app N).hom.app (op (parameter P))).hom m)

attribute [instance] NormalizedModules.additive NormalizedModules.equivalence
  NormalizedModules.limits NormalizedModules.colimits NormalizedModules.inverseAdditive

variable {k Ω} {h : FieldActionTopos.Normalization k Ω}
  {R : CategoryTheory.CondensedBar.Ring.{u}}
  [CategoryTheory.CondensedBar.ActionAbelian R (Ω ≃ₐ[k] Ω)]
  [HasDerivedCategory.{u + 2}
    (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X)]
  [HasDerivedCategory.{u + 2}
    (Profinite.CondensedAction.ActionModule R.toMon (Ω ≃ₐ[k] Ω))]

/-- The geometric section functor is the actual module pushforward followed by E_R.
Source: Stacks 03D6 (blueprint: lem-sfb-geometric-sections-adjunction). -/
abbrev geometricFunctor (e : NormalizedModules k Ω h R)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) := CondensedRing.lowerStar R.X a ⋙ e.functor

/-- The specified left adjoint is actual pullback after the inverse field equivalence.
Source: Stacks 03D7 (blueprint: lem-sfb-geometric-sections-adjunction). -/
abbrev geometricLeft (e : NormalizedModules k Ω h R)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) :=
  e.functor.asEquivalence.inverse ⋙ CondensedRing.upperStar R.X a

/-- Exactly the composite adjunction, including its unit, counit and Hom bijection.
Source: Stacks 03D7, Categories 0DV0 (blueprint: lem-sfb-geometric-sections-adjunction). -/
def geometricAdjunction (e : NormalizedModules k Ω h R)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) : geometricLeft e a ⊣ geometricFunctor e a :=
  e.functor.asEquivalence.symm.toAdjunction.comp
    (CondensedRing.upperStarLowerStarAdjunction R.X a)

/-- Evaluate the actual composite on the base-changed free test. The displayed target
is M(X times_s bar s[P]); its X^s[P] coordinates are fixed by GeometricNormalization.
Naturality, scalars and variable right translations are the field formulas applied
to the actual lowerStar module, whose coefficient action is its original unit action.
Source: Bhatt--Scholze Example 4.1.10; Stacks 03D6
(blueprint: lem-sfb-geometric-sections-adjunction). -/
def geometricSection (e : NormalizedModules k Ω h R)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientRing X R.toMon).X)
    (P : Base.{u}) :
    ((geometricFunctor e a).obj M).module.X.obj.obj (op (parameter P)) ≃+
      M.X.obj.obj (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj
        ((Scheme.ProEt.qcqsInclusion _).obj (h.free.obj ⟨P⟩)))) :=
  e.sections ((CondensedRing.lowerStar R.X a).obj M) P

/-- The geometric section formula in its canonical X, separable-closure and profinite
coordinates. The section map itself is geometricSection, not arbitrary comparison data.
Source: Bhatt--Scholze Examples 4.1.9--4.1.10; Stacks 03D6
(blueprint: lem-sfb-geometric-sections-adjunction). -/
structure GeometricNormalization (e : NormalizedModules k Ω h R)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) where
  /-- Additivity of a^* E_R^{-1}, with the real geometricAdjunction. -/
  leftAdditive : (geometricLeft e a).Additive
  /-- The original X-module category is Grothendieck abelian. -/
  grothendieck : IsGrothendieckAbelian.{u + 1}
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientRing X R.toMon).X)
  /-- The canonical test isomorphism X times_s bar s[P] to X^s[P]. -/
  tests (P : Base.{u}) :
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj
      ((Scheme.ProEt.qcqsInclusion _).obj (h.free.obj ⟨P⟩))).left ≅
        ((profiniteToProEtOf
          (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj (parameter P)).left
  /-- The X-coordinate is unchanged. -/
  tests_base (P : Base.{u}) :
    (tests P).hom ≫ ((profiniteToProEtOf
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj (parameter P)).hom ≫
        pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) =
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj
        ((Scheme.ProEt.qcqsInclusion _).obj (h.free.obj ⟨P⟩))).hom
  /-- The separable-closure coordinate is unchanged. -/
  tests_geometric (P : Base.{u}) :
    (tests P).hom ≫ ((profiniteToProEtOf
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj (parameter P)).hom ≫
        pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) =
      pullback.fst ((Scheme.ProEt.qcqsInclusion _).obj (h.free.obj ⟨P⟩)).hom a ≫
        (h.geometric P).hom.left ≫
          ((profiniteToProEtOf (Spec (.of Ω))).obj (parameter P)).hom
  /-- The profinite coordinate is unchanged, fixing the entire test isomorphism. -/
  tests_parameter (P : Base.{u}) :
    (tests P).hom ≫ pullback.fst (toSpecZ (profiniteToScheme.obj (parameter P)))
        (toSpecZ (pullback a (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))) =
      pullback.fst ((Scheme.ProEt.qcqsInclusion _).obj (h.free.obj ⟨P⟩)).hom a ≫
        (h.geometric P).hom.left ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj (parameter P))) (toSpecZ (Spec (.of Ω)))

/-- Scalar restriction is the existing comap on the field and ScalarAction on the
action side. The comparison is literally the identity in the fixed section coordinates.
Source: normalized field comparison, arbitrary coefficient-map clause
(blueprint: lem-sfb-geometric-sections-adjunction). -/
structure ScalarNormalization {R' : CategoryTheory.CondensedBar.Ring.{u}}
    [CategoryTheory.CondensedBar.ActionAbelian R' (Ω ≃ₐ[k] Ω)]
    [HasDerivedCategory.{u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (coefficientRing (Spec (.of k)) R'.toMon).X)]
    [HasDerivedCategory.{u + 2}
      (Profinite.CondensedAction.ActionModule R'.toMon (Ω ≃ₐ[k] Ω))]
    (e : NormalizedModules k Ω h R) (e' : NormalizedModules k Ω h R') (φ : R ⟶ R') where
  /-- Restriction retains the underlying sheaf and all generalized action maps. -/
  restriction : CategoryTheory.CondensedBar.ScalarAction φ (Ω ≃ₐ[k] Ω)
  /-- The commuting square uses actual scalar restriction, with no flatness assumption. -/
  comparison : Mod.comap ((upperStarFromPoint (Spec (.of k))).map φ.hom.hom) ⋙ e.functor ≅
    e'.functor ⋙ restriction.functor
  /-- On the section groups the comparison is the identity. -/
  sections (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R'.toMon).X) (P : Base.{u})
      (m : (e.functor.obj ((Mod.comap
        ((upperStarFromPoint (Spec (.of k))).map φ.hom.hom)).obj N)).module.X.obj.obj
          (op (parameter P))) :
    e'.sections N P
      (((restriction.underlying.hom.app (e'.functor.obj N)).hom.hom.app
        (op (parameter P))).hom
          ((((comparison.hom.app N).val).hom.hom.app (op (parameter P))).hom m)) =
      e.sections ((Mod.comap ((upperStarFromPoint (Spec (.of k))).map φ.hom.hom)).obj N) P m

variable (k Ω)

/-- All rings and ring maps are quantified simultaneously. Standard localizations
supply the ordinary unbounded derived categories, without new size hypotheses.
Source: blueprint paragraph (3) (blueprint: lem-sfb-geometric-sections-adjunction). -/
def Assertion (h : FieldActionTopos.Normalization k Ω)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) : Prop := by
  refine ∃ ab : ∀ R : CategoryTheory.CondensedBar.Ring.{u},
    CategoryTheory.CondensedBar.ActionAbelian R (Ω ≃ₐ[k] Ω), ?_
  letI (R : CategoryTheory.CondensedBar.Ring.{u}) :
      CategoryTheory.CondensedBar.ActionAbelian R (Ω ≃ₐ[k] Ω) := ab R
  letI (R : CategoryTheory.CondensedBar.Ring.{u}) : HasDerivedCategory.{u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
        (coefficientRing (Spec (.of k)) R.toMon).X) := HasDerivedCategory.standard _
  letI (R : CategoryTheory.CondensedBar.Ring.{u}) : HasDerivedCategory.{u + 2}
      (Profinite.CondensedAction.ActionModule R.toMon (Ω ≃ₐ[k] Ω)) :=
    HasDerivedCategory.standard _
  exact ∃ e : ∀ R : CategoryTheory.CondensedBar.Ring.{u}, NormalizedModules k Ω h R,
    (∀ R : CategoryTheory.CondensedBar.Ring.{u}, Nonempty (GeometricNormalization (e R) X a)) ∧
    (∀ (R R' : CategoryTheory.CondensedBar.Ring.{u}) (φ : R ⟶ R'),
      Nonempty (ScalarNormalization (e R) (e R') φ))

/-- Normalized module transport, geometric sections, scalar restriction, ordinary
unbounded derived equivalence and the actual invariant-section adjunction.

Source: current blueprint, direct-images proof paragraph (3), agent structural input;
Bhatt--Scholze Examples 4.1.9--4.1.10; Stacks 03D6, 03D7, 08BJ
(blueprint: lem-sfb-geometric-sections-adjunction).

Proof:
1. Lift h and its ring comparison by lem-weil-pbc-ringed-presentation-transport,
   lem-sfb-internal-action-site-presentation and the internal/section-module equivalence.
   Use h.sections as the underlying free-test coordinates. The point unit followed by
   h.cover is the scalar map; its normalization agrees with h.coefficientComparison.
   The labeled restriction is b acting on f-star, also for variable b.
2. The equivalence is additive and exact. Apply ringed-presentation-transport and
   lem-sfb-section-ring-lax-pushforward-coherence termwise. The inverse transports
   acyclic complexes and null-homotopies, proving K-injective preservation both ways;
   localize the termwise unit and counit to obtain the ordinary unbounded equivalence.
3. Scalar restriction retains sections, restrictions and actions and precomposes scalars
   by phi. Naturality of the normalized ring comparison gives the identity on sections,
   including nonflat maps, identity maps and maps into the zero ring.
4. Evaluate actual module lowerStar on h.free. Base change gives X times_s bar s[P].
   Apply lem-sfb-relative-profinite-test-labels: the X, separable-closure and profinite
   coordinates uniquely identify it with X^s[P]. geometricSection is exactly this
   evaluation. Its scalar action is lowerStar_obj_smul; labeled arrows are the
   base-changed free arrows, hence the prescribed right translations.
5. Compose the inverse-equivalence adjunction with the actual module adjunction of
   sk-def-sfb-module-pushforward-pullback. This is geometricAdjunction, with additive
   left adjoint a^* E_R^{-1} and precisely the composite unit, counit and Hom bijection.
6. Apply lem-weil-pbc-ring-sheaves-grothendieck and the internal/section equivalence.
   Apply lem-sfb-sheaf-action-grothendieck-inflation to get the action category and exact
   trivial inflation. This gives all four Grothendieck categories with their old addition.
7. Use lem-sfb-sheaf-product-fixed-adjunction for sections fixed after every base change.
   The existing Invariants specification includes both codomain-restriction formulas.
   Lift h's point comparison to modules by lem-weil-pbc-ringed-topoi-module-adjunction:
   its unit and counit become the actual abelian point-adjunction unit and counit under
   pointUnderlying. Its inclusion is restriction along h.cover, and pointMate fixes its
   conjugacy with pointPull. This characterizes actual module direct image, not merely
   an abstract right adjoint. Zero rings, trivial G and empty tests and schemes remain.
-/
theorem geometric_sections_adjunction (h : FieldActionTopos.Normalization k Ω)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X] :
    Assertion k Ω h X a := by
  sorry

end AlgebraicGeometry.ProEtale.GeometricSectionsAdjunction
