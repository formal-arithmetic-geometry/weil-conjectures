/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

import Sheaf.Topology.StoneanCover
import Sheaf.RingTheory.StoneanCoverSecondStage
import Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleFiniteProjectiveDualizable
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.Algebra.Homology.LocallyFreeDerivedHom
import Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence
import Sheaf.Paper.ComponentRelativeProfiniteSite
import Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation
import Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor

/-!
# Lisse condensed cohomology on w-strictly local affines

Source: Hemo--Richarz--Scholbach, Lemma 4.1, Proposition 4.3, equation (4.2),
and Corollary 4.7; Bhatt--Scholze, Lemma 2.2.8.
(blueprint: lem-sfb-wstrict-lisse-component-cohomology).

The map below is constructed from the actual derived module adjunction unit.
Sections are the recorded terminal-object evaluation with scalars forgotten.
All derived categories are ordinary, uncompleted derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical terminal-section comparison for module direct image, forgetting scalars.
Source: HRS, Section 3, derived sections convention; final-object base change.
(blueprint: lem-sfb-wstrict-lisse-component-cohomology). -/
def componentModuleSectionsLowerStarIso :
    lowerStar Λ.X f ⋙ condensedModuleSections Λ.X Y ≅ condensedModuleSections Λ.X X :=
  Functor.isoWhiskerLeft
      (lowerStar Λ.X f ⋙ Mod.forget (condensedRingObj Λ.X Y))
      (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Y) Ab.{u + 1}
        (Scheme.ProEt.isTerminalMkId Y)).symm ≪≫
    Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ.X X))
      (globalSectionsLowerStarIso Ab.{u + 1} f) ≪≫
    Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ.X X))
      (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) Ab.{u + 1}
        (Scheme.ProEt.isTerminalMkId X))

/-- Module pushforward preserves K-injective complexes because its left adjoint is exact.
Source: the derived adjunction convention in HRS, Section 3.
(blueprint: lem-sfb-wstrict-lisse-component-cohomology). -/
instance componentLowerStar_preservesKInjectiveComplexes :
    (lowerStar Λ.X f).PreservesKInjectiveComplexes :=
  (upperStarLowerStarAdjunction Λ.X f).preservesKInjectiveComplexes

/-- The unit-normalized Leray comparison for ordinary derived module sections.
Source: HRS, Section 3, composition of derived direct images.
(blueprint: lem-sfb-wstrict-lisse-component-cohomology). -/
def componentModuleDerivedSectionsLowerStarIso :
    moduleObjectDerivedPushforward Λ.X f ⋙
        (condensedModuleSections Λ.X Y).rightDerivedFunctor ≅
      (condensedModuleSections Λ.X X).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompIso' (lowerStar Λ.X f) (condensedModuleSections Λ.X Y)
    (componentModuleSectionsLowerStarIso Λ f)

/-- Pullback of derived sections induced by the actual derived module adjunction unit.
It is a natural transformation on the full ordinary derived category.
Source: HRS, Proposition 4.3 and Corollary 4.7, canonical section pullback.
(blueprint: lem-sfb-wstrict-lisse-component-cohomology). -/
def componentDerivedSectionsPullback :
    (condensedModuleSections Λ.X Y).rightDerivedFunctor ⟶
      moduleObjectDerivedPullback Λ.X f ⋙
        (condensedModuleSections Λ.X X).rightDerivedFunctor :=
  Functor.whiskerRight (derivedUpperStarLowerStarAdjunction Λ.X f).unit
      (condensedModuleSections Λ.X Y).rightDerivedFunctor ≫
    Functor.whiskerLeft (moduleObjectDerivedPullback Λ.X f)
      (componentModuleDerivedSectionsLowerStarIso Λ f).hom

/-- The same adjunction-unit map on degree-zero modules, with its target identified with
ordinary exact pullback in degree zero. Naturality in modules is part of this data.
Source: HRS, Proposition 4.3 and equation (4.2), degree-zero finite free case.
(blueprint: lem-sfb-wstrict-lisse-component-cohomology). -/
def componentLisseSectionsPullback :
    DerivedCategory.singleFunctor _ 0 ⋙
        (condensedModuleSections Λ.X Y).rightDerivedFunctor ⟶
      upperStar Λ.X f ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        (condensedModuleSections Λ.X X).rightDerivedFunctor :=
  Functor.whiskerLeft (DerivedCategory.singleFunctor _ 0)
      (componentDerivedSectionsPullback Λ f) ≫
    Functor.whiskerRight (upperStar Λ.X f).singleFunctorCompLeftDerivedFunctorIso.hom
      (condensedModuleSections Λ.X X).rightDerivedFunctor

/-- The unit-induced section pullback respects composition through the canonical
pullback comparison. Together with naturality of `componentLisseSectionsPullback`,
this gives naturality for every commutative diagram of the morphisms in the main theorem.
Source: HRS, Corollary 4.7; derived adjunction units and composition comparisons.
(blueprint: lem-sfb-wstrict-lisse-component-cohomology).

Proof: compose the two underived module adjunctions. The unit of the composite is
its first unit followed by direct image of the second unit. The comparison
`upperStarComp` is the mate of `lowerStarComp`, so it carries that composite unit
to the unit of the composite scheme map. Derive this identity and apply terminal
sections. The Leray comparisons used above are the unit-normalized comparisons;
their associativity and the single-degree comparisons identify the two displayed
maps. Equality of the two factorizations of a commutative diagram then gives the
same equality for that diagram, independently of every hypercover choice. -/
theorem componentLisseSectionsPullback_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ.X Z)) :
    (componentLisseSectionsPullback Λ (f ≫ g)).app M ≫
        (condensedModuleSections Λ.X X).rightDerivedFunctor.map
          ((DerivedCategory.singleFunctor _ 0).map ((upperStarComp Λ.X f g).hom.app M)) =
      (componentLisseSectionsPullback Λ g).app M ≫
        (componentLisseSectionsPullback Λ f).app ((upperStar Λ.X g).obj M) := by
  sorry

/-- On w-strictly local affines a component homeomorphism preserves the ordinary derived
sections of every finite-rank lisse condensed module, by the actual adjunction-unit map.
There is no restriction on the condensed ring or on the profinite component spaces.
Source: HRS, Lemma 4.1, Proposition 4.3 and (4.2), Corollary 4.7; the w-strictly local
extension uses Bhatt--Scholze, Lemma 2.2.8.
(blueprint: lem-sfb-wstrict-lisse-component-cohomology).

Proof, following the nine DAG steps:
1. Identify the two component spaces via the given homeomorphism. Empty components
mean both schemes are empty and all section complexes are zero. Point pullback
comparisons identify coefficients; exact module pullback identifies degree-zero
pullback with its ordinary total derived functor. Internal-to-section-module
transport identifies these adjunctions and their actual units.
2. Resolve the common profinite space by a finite-basis hypercover of extremally
disconnected profinite spaces, using the Stonean cover theorem. Finite disjoint
unions of the basis objects remain extremally disconnected; finite matching limits
distribute over the summands, so this is a hypercover by actual profinite spaces.
3. Apply the relative component construction to both schemes. It preserves matching
limits and coverings. Its terms are w-contractible affines by the second-stage
w-contractible-cover theorem, with identical component spaces in corresponding
degrees. The induced maps commute with all faces, degeneracies and augmentations.
4. Restrict the lisse module to these terms. Local finite free duals give ordinary
module duality; tensor is exact locally, hence the degree-zero complexes are K-flat
and dualizable in the ordinary derived category, also in rank zero.
5. The w-contractible lisse evaluation equivalences identify each such module with
one on the component space. Full faithfulness identifies pullback on Hom from the
coefficient unit with the identity on the common component space. The ringed-derived
monoidal comparisons identify precisely these pullback functors and their units.
6. The locally free derived-Hom formula, normalized by evaluation on 1, identifies
this Hom map with the actual section pullback. The contractible-derived-sections
theorem identifies the section objects with degree-zero section modules.
7. The resulting degreewise bijections commute with face restrictions. They give
an isomorphism of nonnegative alternating-face cochain complexes: the inverses
commute with differentials by the same cochain-map equation.
8. Acyclic-hypercover pullback normalization identifies this cochain map with the
specified adjunction-unit map, under augmentation-normalized derived-section
comparisons. Thus this particular map is invertible in the ordinary derived
category of abelian groups; no arbitrary unbounded totalization is used.
9. Naturality in the module is built into the natural transformation above.
The composition theorem above gives compatibility for commutative diagrams,
using the canonical pullback composition comparisons. The hypercover served only
to test invertibility, so the map itself contains no hypercover choice. -/
theorem wstrict_lisse_component_cohomology
    [IsAffine X] [IsAffine Y]
    [IsWStrictlyLocalRing Γ(X, ⊤)] [IsWStrictlyLocalRing Γ(Y, ⊤)]
    (hcomponents : IsHomeomorph f.continuous.connectedComponentsMap)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y))
    (hM : IsLisseCoefficientModule Λ.X M) :
    IsIso ((componentLisseSectionsPullback Λ f).app M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
