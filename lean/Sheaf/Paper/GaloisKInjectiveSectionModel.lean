/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.GeometricSectionsAdjunction
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Sites.EpiMono
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization

/-! # The normalized unbounded Galois section model

Source: Stacks Project, Derived Categories, Tags 08BJ, 070K, 070Y and 09T5;
Bhatt--Scholze, Examples 4.1.9--4.1.10; the agent refinement of the geometric
section comparison (blueprint: lem-sfb-galois-kinjective-section-model).

All categories are the original internal module categories. The comparison is
specified by restriction and the canonical total-right-derived composition maps.
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

namespace AlgebraicGeometry.ProEtale.GaloisKInjectiveSectionModel

open GeometricSectionsAdjunction

/-- The singleton in the existing small presentation of the profinite site.
Source: Bhatt--Scholze Example 4.1.10
(blueprint: lem-sfb-galois-kinjective-section-model). -/
abbrev singleton : Base.{u} := ⟨Profinite.of PUnit.{u + 1}⟩

/-- Evaluation of the underlying condensed abelian sheaf at the singleton.
Source: Bhatt--Scholze Example 4.1.10
(blueprint: lem-sfb-galois-kinjective-section-model). -/
abbrev singletonEvaluation (R : CategoryTheory.CondensedBar.Ring.{u}) :
    Profinite.CondensedAction.Modules R.toMon ⥤ Ab.{u + 1} :=
  Mod.forget R.toMon.X ⋙
    (sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj (op (parameter singleton))

/-- Global sections of the original internal module, evaluated at the final test.
This is the section realization of Hom_R(R,-) in the hypercohomology convention.
Source: Stacks 07A5, 08JA
(blueprint: lem-sfb-galois-kinjective-section-model). -/
abbrev globalSections (R : CategoryTheory.CondensedBar.Ring.{u}) (X : Scheme.{u}) :=
  Mod.forget (condensedRingObj R.X X) ⋙
    (sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).obj (op (Scheme.ProEt.mk (𝟙 X)))

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
  {h : FieldActionTopos.Normalization k Ω}
  {R : CategoryTheory.CondensedBar.Ring.{u}}
  [CategoryTheory.CondensedBar.ActionAbelian R (Ω ≃ₐ[k] Ω)]
  [HasDerivedCategory.{u + 2}
    (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (coefficientRing (Spec (.of k)) R.toMon).X)]
  [HasDerivedCategory.{u + 2}
    (Profinite.CondensedAction.ActionModule R.toMon (Ω ≃ₐ[k] Ω))]

/-- The named free geometric test over X; the dependency identifies it canonically
with X^s[P], retaining its three coordinates.
Source: normalized geometric section adjunction, Bhatt--Scholze Example 4.1.10
(blueprint: lem-sfb-galois-kinjective-section-model). -/
abbrev geometricTest {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (P : Base.{u}) : X.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).obj
    ((Scheme.ProEt.qcqsInclusion _).obj (h.free.obj ⟨P⟩))

/-- Restrict sections from X to its geometric free singleton test, in the fixed
geometric-section coordinates. This uses an actual site restriction map.
Source: Bhatt--Scholze Examples 4.1.9--4.1.10
(blueprint: lem-sfb-galois-kinjective-section-model). -/
def geometricRestriction (e : NormalizedModules k Ω h R)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R.X X)) :
    ((globalSections R X).obj M) →+
      ((geometricFunctor e a).obj M).module.X.obj.obj
        (op (parameter singleton)) :=
  (geometricSection e a M singleton).symm.toAddMonoidHom.comp
    (M.X.obj.map (MorphismProperty.Over.homMk
      (geometricTest (h := h) a singleton).hom :
        geometricTest (h := h) a singleton ⟶ Scheme.ProEt.mk (𝟙 X)).op).hom

set_option maxHeartbeats 800000 in
-- The specification elaborates the three compatible localizations and their canonical comparisons.
/-- The full section-model specification. Exactness, resolutions and preservation
are conclusions. The isomorphism gamma is pinned down by the actual restriction map;
its inverse is the unique preimage under the fixed-section inclusion. The last two
fields specify canonical derived composition and its arbitrary-resolution coordinates.
Source: Stacks 08BJ, 070K, 070Y, 09T5; Bhatt--Scholze Example 4.1.10
(blueprint: lem-sfb-galois-kinjective-section-model). -/
structure Model (e : NormalizedModules k Ω h R)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
    [HasDerivedCategory.{u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R.X X))]
    [HasDerivedCategory.{u + 2} (Profinite.CondensedAction.Modules R.toMon)]
    [HasDerivedCategory.{u + 2} Ab.{u + 1}] where
  /-- The section functors retain the actual addition of module maps. -/
  [evaluationAdditive : (singletonEvaluation R).Additive]
  [globalAdditive : (globalSections R X).Additive]
  [geometricAdditive : (geometricFunctor e a).Additive]
  [evaluationZero : (singletonEvaluation R).PreservesZeroMorphisms]
  [globalZero : (globalSections R X).PreservesZeroMorphisms]
  [geometricZero :
    (geometricFunctor e a).PreservesZeroMorphisms]
  [invariantsZero : e.invariants.functor.PreservesZeroMorphisms]
  [compositeZero : ((geometricFunctor e a ⋙
    e.invariants.functor) ⋙ singletonEvaluation R).PreservesZeroMorphisms]
  /-- Exact singleton evaluation: kernels and cokernels. -/
  [evaluationLimits : PreservesFiniteLimits (singletonEvaluation R)]
  [evaluationColimits : PreservesFiniteColimits (singletonEvaluation R)]
  /-- The specified additive left adjoint is exact for every R. -/
  [leftAdditive : (geometricLeft e a).Additive]
  [leftLimits : PreservesFiniteLimits (geometricLeft e a)]
  [leftColimits : PreservesFiniteColimits (geometricLeft e a)]
  /-- The original right adjoints preserve unbounded K-injective complexes. -/
  [geometricKInjective :
    (geometricFunctor e a).PreservesKInjectiveComplexes]
  [invariantsKInjective : e.invariants.functor.PreservesKInjectiveComplexes]
  /-- Every unbounded complex has a K-injective resolution, in each category. -/
  [sourceResolutions : Abelian.HasKInjectiveResolutions
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R.X X))]
  [condensedResolutions :
    Abelian.HasKInjectiveResolutions (Profinite.CondensedAction.Modules R.toMon)]
  [actionResolutions : Abelian.HasKInjectiveResolutions
    (Profinite.CondensedAction.ActionModule R.toMon (Ω ≃ₐ[k] Ω))]
  /-- Restriction with invariant codomain, as an isomorphism of additive functors. -/
  gamma : globalSections R X ≅
    (geometricFunctor e a ⋙ e.invariants.functor) ⋙
      singletonEvaluation R
  /-- Inclusion of gamma is precisely restriction to X^s; this fixes gamma uniquely. -/
  restriction (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R.X X)) (m : (globalSections R X).obj M) :
    (((e.invariants.inclusion.app
        ((geometricFunctor e a).obj M)).hom.hom.app
          (op (parameter singleton))).hom ((gamma.hom.app M).hom m)) =
      geometricRestriction e a M m
  /-- Unique gluing is the inverse, for every invariant section. -/
  gluing (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R.X X))
      (m : ((geometricFunctor e a ⋙ e.invariants.functor) ⋙
        singletonEvaluation R).obj M) :
    ∃! t : (globalSections R X).obj M,
      geometricRestriction e a M t =
        (((e.invariants.inclusion.app
          ((geometricFunctor e a).obj M)).hom.hom.app
            (op (parameter singleton))).hom m)
  /-- The actual natural derived comparison, on ordinary unbounded derived categories. -/
  comparison : (globalSections R X).rightDerivedFunctor.{_, _, _, _, u + 2, u + 2} ≅
    ((geometricFunctor e a).rightDerivedFunctor.{_, _, _, _, u + 2, u + 2} ⋙
      e.invariants.functor.rightDerivedFunctor.{_, _, _, _, u + 2, u + 2}) ⋙
        (singletonEvaluation R).mapDerivedCategory.{u + 2, u + 2}
  /-- Canonical right-derived composition, followed by exact singleton evaluation. -/
  canonical : comparison =
    Functor.rightDerivedFunctorNatIso.{_, _, _, _, u + 2, u + 2} gamma ≪≫
      Functor.rightDerivedFunctorCompMapDerivedCategoryIso.{u + 2, u + 2, u + 2}
        (geometricFunctor e a ⋙ e.invariants.functor)
        (singletonEvaluation R) ≪≫
      Functor.isoWhiskerRight
        (Functor.rightDerivedFunctorCompIso.{_, _, _, _, _, _, u + 2, u + 2, u + 2}
          (geometricFunctor e a) e.invariants.functor)
        (singletonEvaluation R).mapDerivedCategory.{u + 2, u + 2}
  /-- On every K-injective resolution the comparison is the localized chain gamma.
  The comparison is natural as a functor isomorphism; quantification over every
  resolution includes the canonical identity changes and their cocycles. -/
  resolution (M I : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R.X X)) ℤ)
      [I.IsKInjective] (i : M ⟶ I) [QuasiIso i] :
    (globalSections R X).rightDerivedFunctor.{_, _, _, _, u + 2, u + 2}.map
        (DerivedCategory.Q.{u + 2}.map i) ≫
        ((globalSections R X).rightDerivedFunctorObjQIso.{_, _, _, _, u + 2, u + 2} I).hom ≫
        DerivedCategory.Q.{u + 2}.map ((NatIso.mapHomologicalComplex gamma (.up ℤ)).hom.app I) =
      comparison.hom.app (DerivedCategory.Q.{u + 2}.obj M) ≫
        (singletonEvaluation R).mapDerivedCategory.{u + 2, u + 2}.map
          (e.invariants.functor.rightDerivedFunctor.{_, _, _, _, u + 2, u + 2}.map
              ((geometricFunctor e a).rightDerivedFunctor.{_, _, _, _, u + 2, u + 2}.map
                (DerivedCategory.Q.{u + 2}.map i)) ≫
            e.invariants.functor.rightDerivedFunctor.{_, _, _, _, u + 2, u + 2}.map
              (((geometricFunctor e a).rightDerivedFunctorObjQIso.{_, _, _, _, u + 2, u + 2}
                  I).hom) ≫
            (e.invariants.functor.rightDerivedFunctorObjQIso.{_, _, _, _, u + 2, u + 2}
              (((geometricFunctor e a).mapHomologicalComplex
                (.up ℤ)).obj I)).hom) ≫
        (singletonEvaluation R).mapDerivedCategoryFactors.{u + 2, u + 2}.hom.app
          ((e.invariants.functor.mapHomologicalComplex (.up ℤ)).obj
            (((geometricFunctor e a).mapHomologicalComplex
              (.up ℤ)).obj I))

/-- Standard compatible localizations, with all substantive conclusions in Model.
Source: Stacks 070K, 070Y and the blueprint size convention
(blueprint: lem-sfb-galois-kinjective-section-model). -/
def Assertion (e : NormalizedModules k Ω h R)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) : Prop := by
  letI : HasDerivedCategory.{u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R.X X)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 2} (Profinite.CondensedAction.Modules R.toMon) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 2} Ab.{u + 1} := HasDerivedCategory.standard _
  exact Nonempty (Model e X a)

/-- Exact singleton evaluation and the normalized unbounded K-injective section model.
Source: Stacks 08BJ, 070K, 070Y, 09T5; Bhatt--Scholze Examples 4.1.9--4.1.10
(blueprint: lem-sfb-galois-kinjective-section-model).

Proof:
1. Use the internal/section-module equivalence and sectionwise kernels. Module
   epimorphisms are locally surjective (lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective).
   A finite jointly surjective cover of the singleton has a nonempty member; a point
   splits its map to the singleton. Restrict a local lift along this section. Thus
   singleton evaluation preserves epimorphisms and is exact, after forgetting scalars.
2. Apply the normalized field/action comparison to the actual module lowerStar of M.
   The pointRestriction and geometricSection formulas of
   lem-sfb-geometric-sections-adjunction identify its invariant inclusion with the
   restriction map geometricRestriction. The sheaf equalizer gives unique gluing.
   All maps commute with module maps, addition and differentials, giving gamma.
3. det-prop-sfb-module-pullback-exact-main makes actual a-star exact. The inverse
   module equivalence is exact, so geometricLeft is exact. Apply
   lem-weil-pbc-right-adjoint-preserves-kinjective to geometricAdjunction and the
   invariant adjunction with exact trivial inflation. Both right adjoints preserve
   K-injectives; this uses no cohomological-dimension bound.
4. All three original categories are Grothendieck by
   lem-sfb-geometric-sections-adjunction. Apply lem-sfb-grothendieck-k-injective.
   The ordinary total right derived functors therefore exist on every unbounded
   complex (lem-weil-pbc-kinjective-total-derived). Their units on I and F(I) are
   invertible, giving the two displayed resolution computations.
5. Apply gamma degreewise. Its naturality at every differential gives a chain
   isomorphism. Exact evaluation descends termwise by
   lem-weil-pbc-exact-functor-derived-factorization. The resolution equation is
   naturality of the derived units and this degreewise chain map.
6. For every derived morphism use the unique homotopy class between resolutions
   of lem-sf-kinjective-derived-map-computation. Naturality of gamma on that class
   gives the comparison square. Identities give change-of-resolution compatibility
   and composition gives its cocycle, for arbitrary quasi-isomorphic resolutions.
7. Apply lem-sfb-derived-composition-adjunction-normalization to trivial inflation
   followed by geometricLeft, with the composite adjunction and identity compositor.
   Its right comparison is the canonical rightDerivedFunctorCompIso, with the
   specified underived units and counits. Postcompose with exact singleton evaluation
   and the normalized gamma. This gives canonical and the resolution formula.
-/
theorem galois_kinjective_section_model
    (e : NormalizedModules k Ω h R)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X] :
    Assertion e X a := by
  sorry

end AlgebraicGeometry.ProEtale.GaloisKInjectiveSectionModel
