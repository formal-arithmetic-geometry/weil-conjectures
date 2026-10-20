/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.TraceFormula.OrientedPointCohomology
public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import Sheaf.Paper.QcqsOrientedTriplePresentation
import WeilConjectures.CategoryTheory.ColimitSites
import Sheaf.CategoryTheory.CohomologyColimitSites
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.DerivedAdjunctionShift
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.Paper.OrientedTripleLimitDescent

/-! # Continuity of derived cohomology of oriented étale products

Source: ILO, Exposé XI §§1.10(b), 2.5--2.7; Stacks Project, Tag 09YP
(blueprint: lem-trf-oriented-derived-cohomology-continuity).

## Main definitions and statements

* `site`, `Modules`, `DPlus`: the recorded oriented triple site and its module sheaves.
* `cohomologyPullback`: the derived map of the ordinary inverse-image adjunction unit.
* `cohomologyDiagram`, `continuityCocone`: the opposite-slice diagram and canonical cocone.
* `restriction_limitSquare`: compatibility of its legs with restriction of inverse systems.
* `orientedDerivedCohomology_continuity`: that cocone is colimiting, naturally in the complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedDerivedContinuity

/-- A diagram X → S ← Y, as a functor on Mathlib's walking cospan.
Source: ILO XI §2.7 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
abbrev Diagram := WalkingCospan ⥤ Scheme.{u}

/-- The existing oriented triple site of the two arrows of a diagram.
Source: ILO XI §1.1 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
abbrev site (d : Diagram.{u}) :=
  CategoryTheory.OrientedPointCohomology.datum.{u, v}
    (d.map WalkingCospan.Hom.inl) (d.map WalkingCospan.Hom.inr)

/-- Finite limits of triples, from the recorded oriented-site interface.
Source: ILO XI §1.1 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
instance site_finiteLimits (d : Diagram.{u}) : HasFiniteLimits (site.{u, v} d).objects :=
  CategoryTheory.OrientedPointCohomology.triples_finiteLimits
    (d.map WalkingCospan.Hom.inl) (d.map WalkingCospan.Hom.inr)

/-- The canonical base-change commutation isomorphism of an arrow in a scheme diagram.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def squareIso {d e : Diagram.{u}} (p : e ⟶ d)
    {i j : WalkingCospan} (a : i ⟶ j) :
    etaleBaseChange.{u, v + 1} (d.map a) ⋙ etaleBaseChange (p.app i) ≅
      etaleBaseChange (p.app j) ⋙ etaleBaseChange (e.map a) :=
  (etaleBaseChangeComp (p.app i) (d.map a)).symm ≪≫
    eqToIso (congrArg (fun f ↦ etaleBaseChange.{u, v + 1} f) (p.naturality a).symm) ≪≫
      etaleBaseChangeComp (e.map a) (p.app j)

/-- The product of the two base-change commutation maps, with no choice of an arrow.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def squarePair {d e : Diagram.{u}} (p : e ⟶ d) :
    ((etaleBaseChange.{u, v + 1} (d.map WalkingCospan.Hom.inl)).prod'
      (etaleBaseChange (d.map WalkingCospan.Hom.inr))) ⋙
        (etaleBaseChange (p.app .left)).prod (etaleBaseChange (p.app .right)) ⟶
    etaleBaseChange (p.app .one) ⋙
      ((etaleBaseChange (e.map WalkingCospan.Hom.inl)).prod'
        (etaleBaseChange (e.map WalkingCospan.Hom.inr))) :=
  NatTrans.prod' (squareIso p WalkingCospan.Hom.inl).hom
    (squareIso p WalkingCospan.Hom.inr).hom

/-- Pull back all three étale neighbourhoods along the component maps of p.
The structural arrows use the canonical fibre-product associativity isomorphisms.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def baseChange {d e : Diagram.{u}} (p : e ⟶ d) : (site.{u, v} d).objects ⥤
    (site.{u, v} e).objects :=
  Comma.map
    (Functor.rightUnitor ((etaleBaseChange.{u, v + 1} (p.app .left)).prod
      (etaleBaseChange (p.app .right))) ≪≫ (Functor.leftUnitor _).symm).hom
    (squarePair p)

/-- Triple base change preserves finite limits and the three generating covering types.
Source: ILO XI §§1.9, 2.5 (blueprint: lem-trf-oriented-derived-cohomology-continuity).
Proof: the comma limits are componentwise, and each étale base-change functor preserves
finite limits. Covers of types (a) and (b) remain covers by scheme base change. A cover
of type (c) remains a type-(c) cover because its defining square remains Cartesian.
The generated-topology criterion gives continuity. -/
theorem baseChange_properties {d e : Diagram.{u}} (p : e ⟶ d) :
    (baseChange.{u, v} p).IsContinuous (site.{u, v} d).topology (site.{u, v} e).topology ∧
      PreservesFiniteLimits (baseChange.{u, v} p) := by
  sorry

/-- Continuity from the generating-cover calculation.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
instance baseChange_continuous {d e : Diagram.{u}} (p : e ⟶ d) :
    (baseChange.{u, v} p).IsContinuous (site.{u, v} d).topology (site.{u, v} e).topology :=
  (baseChange_properties p).1

/-- Finite-limit preservation from componentwise comma limits.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
instance baseChange_finiteLimits {d e : Diagram.{u}} (p : e ⟶ d) :
    PreservesFiniteLimits (baseChange.{u, v} p) := (baseChange_properties p).2

/-- Constant-ring module sheaves on the actual oriented product. The equivalent fixed-ring
encoding keeps the coefficient ring action on every section.
Source: Stacks 03CY; ILO XI §4.1
(blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
abbrev Modules (d : Diagram.{u}) (Λ : Type v) [CommRing Λ] :=
  Sheaf (site.{u, v} d).topology
    (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))

/-- Bounded-below derived constant-ring module sheaves, with Mathlib's standard localization.
Source: ILO XI §4.1 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
abbrev DPlus (d : Diagram.{u}) (Λ : Type v) [CommRing Λ] :=
  DerivedCategory.Plus (Modules d Λ)

/-- Exact inverse image on constant-coefficient module sheaves.
Source: ILO XI §1.9; Stacks 00YV
(blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def pull {d e : Diagram.{u}} (p : e ⟶ d) (Λ : Type v) [CommRing Λ] :
    Modules d Λ ⥤ Modules e Λ :=
  (baseChange.{u, v} p).sheafPullback (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))
    (site.{u, v} d).topology (site.{u, v} e).topology

/-- Global sections are evaluation at the final triple, with their coefficient action.
Source: ILO XI §2.7; Stacks 09YP
(blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def sections (d : Diagram.{u}) (Λ : Type v) [CommRing Λ] :
    Modules d Λ ⥤ ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (⊤_ (site.{u, v} d).objects))

/-- The canonical inverse image is exact and additive.
Source: Stacks 00YV (blueprint: lem-trf-oriented-derived-cohomology-continuity).
Proof: its left adjunction preserves colimits; its finite-limit preservation follows
from flatness of the continuous finite-limit-preserving triple functor. An exact functor
between abelian categories preserves the canonical biproduct addition. -/
theorem pull_properties {d e : Diagram.{u}} (p : e ⟶ d) (Λ : Type v) [CommRing Λ] :
    (pull p Λ).Additive ∧ PreservesFiniteLimits (pull p Λ) ∧
      PreservesFiniteColimits (pull p Λ) := by
  sorry

/-- Additivity of exact constant-coefficient inverse image.
Source: Stacks 00YV (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
instance pull_additive {d e : Diagram.{u}} (p : e ⟶ d) (Λ : Type v) [CommRing Λ] :
    (pull p Λ).Additive := (pull_properties p Λ).1

/-- Left exactness of constant-coefficient inverse image.
Source: Stacks 00YV (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
instance pull_limits {d e : Diagram.{u}} (p : e ⟶ d) (Λ : Type v) [CommRing Λ] :
    PreservesFiniteLimits (pull p Λ) := (pull_properties p Λ).2.1

/-- Right exactness of constant-coefficient inverse image.
Source: Stacks 00YV (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
instance pull_colimits {d e : Diagram.{u}} (p : e ⟶ d) (Λ : Type v) [CommRing Λ] :
    PreservesFiniteColimits (pull p Λ) := (pull_properties p Λ).2.2

/-- The exact inverse image applied termwise and localized at quasi-isomorphisms.
Source: ILO XI §4.1 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def star {d e : Diagram.{u}} (p : e ⟶ d) (Λ : Type v) [CommRing Λ] :
    DPlus d Λ ⥤ DPlus e Λ := (pull p Λ).mapDerivedCategoryPlus

/-- Global sections are additive, because both presheaf forgetting and evaluation are.
Source: Stacks 09YP (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
instance sections_additive (d : Diagram.{u}) (Λ : Type v) [CommRing Λ] :
    (sections d Λ).Additive := inferInstanceAs
      ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj
        (op (⊤_ (site.{u, v} d).objects))).Additive)

/-- Derived global sections, evaluated on injective representatives; these bounded-below
injective representatives are K-injective, so this is total right derived global sections.
Source: Stacks 070H, 09YP (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def RGamma (d : Diagram.{u}) (Λ : Type v) [CommRing Λ] :=
  (sections d Λ).rightDerivedFunctorPlus

/-- All integer-degree module-valued cohomology of derived global sections.
Source: ILO XI §2.7 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def cohomology (d : Diagram.{u}) (Λ : Type v) [CommRing Λ] (n : ℤ) :=
  RGamma d Λ ⋙ DerivedCategory.Plus.homologyFunctor
    (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ)) n

/-- The section map obtained from the actual geometric inverse-image adjunction unit.
Source: ILO XI §2.7 (*); Stacks 0736
(blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def sectionPullbackApp {d e : Diagram.{u}} (p : e ⟶ d) (Λ : Type v) [CommRing Λ]
    (M : Modules d Λ) : (sections d Λ).obj M ⟶ (pull p Λ ⋙ sections e Λ).obj M :=
  (((baseChange.{u, v} p).sheafAdjunctionContinuous
      (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))
      (site.{u, v} d).topology (site.{u, v} e).topology).unit.app M).hom.app
        (op (⊤_ (site.{u, v} d).objects)) ≫
    ((pull p Λ).obj M).obj.map (inv (terminalComparison (baseChange.{u, v} p))).op

/-- The sections pullback is natural in the module sheaf.
Source: Stacks 0736 (blueprint: lem-trf-oriented-derived-cohomology-continuity).
Proof: evaluate naturality of the inverse-image adjunction unit at the final triple,
then use naturality of the pulled-back sheaf morphism along the terminal comparison. -/
theorem sectionPullback_natural {d e : Diagram.{u}} (p : e ⟶ d)
    (Λ : Type v) [CommRing Λ] {M N : Modules d Λ} (f : M ⟶ N) :
    (sections d Λ).map f ≫ sectionPullbackApp p Λ N =
      sectionPullbackApp p Λ M ≫ (pull p Λ ⋙ sections e Λ).map f := by
  sorry

/-- The ordinary global-sections pullback: evaluate the inverse-image adjunction unit
at the final triple and restrict along the inverse terminal comparison. This fixes the
normalization to the actual geometric cohomology pullback.
Source: ILO XI §2.7 (*); Stacks 0736
(blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def sectionPullback {d e : Diagram.{u}} (p : e ⟶ d) (Λ : Type v) [CommRing Λ] :
    sections d Λ ⟶ pull p Λ ⋙ sections e Λ where
  app := sectionPullbackApp p Λ
  naturality := fun _ _ f ↦ sectionPullback_natural p Λ f

/-- Derive the normalized sections pullback, with identity coefficient transport.
The right-derived universal property fixes its compatibility with the ordinary unit.
Source: ILO XI §2.7 (*); Stacks 0736
(blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def derivedPullback {d e : Diagram.{u}} (p : e ⟶ d) (Λ : Type v) [CommRing Λ] :
    RGamma d Λ ⟶ star p Λ ⋙ RGamma e Λ :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))).inv ≫
        Functor.rightDerivedFunctorPlusBaseChange
          ((Functor.rightUnitor (sections d Λ)).hom ≫ sectionPullback p Λ)

/-- The canonical cohomological pullback in every integer degree, natural in K.
Source: ILO XI §2.7 (*); Stacks 09YP
(blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def cohomologyPullback {d e : Diagram.{u}} (p : e ⟶ d)
    (Λ : Type v) [CommRing Λ] (n : ℤ) :
    cohomology d Λ n ⟶ star p Λ ⋙ cohomology e Λ n :=
  Functor.whiskerRight (derivedPullback p Λ)
    (DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ)) n)

/-- Fibre-product associativity uniquely determines triple base-change composition.
The three component equations specify the isomorphism, rather than choosing an arbitrary
one between the two functors.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-derived-cohomology-continuity).
Proof: for each triple take the product of the two canonical étale base-change composition
isomorphisms and the middle composition isomorphism. Associativity of pullback identifies
the comma square. Their naturality gives a natural isomorphism. Equality of the three
components implies equality of comma arrows and hence uniqueness. -/
theorem baseChangeComp_unique {d e f : Diagram.{u}} (p : e ⟶ d) (q : f ⟶ e) :
    ∃! b : baseChange.{u, v} (q ≫ p) ≅ baseChange p ⋙ baseChange q,
      ∀ T : (site.{u, v} d).objects,
        ((b.hom.app T).left.1 =
          (etaleBaseChangeComp (q.app .left) (p.app .left)).hom.app T.left.1) ∧
        ((b.hom.app T).left.2 =
          (etaleBaseChangeComp (q.app .right) (p.app .right)).hom.app T.left.2) ∧
        ((b.hom.app T).right =
          (etaleBaseChangeComp (q.app .one) (p.app .one)).hom.app T.right) := by
  sorry

/-- The uniquely specified composition isomorphism on triple sites.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def baseChangeComp {d e f : Diagram.{u}} (p : e ⟶ d) (q : f ⟶ e) :=
  (baseChangeComp_unique.{u, v} p q).choose

/-- Composition on direct images is precomposition by the specified triple functors.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def directComp {d e f : Diagram.{u}} (p : e ⟶ d) (q : f ⟶ e)
    (Λ : Type v) [CommRing Λ] :=
  Functor.sheafPushforwardContinuousComp' (baseChangeComp.{u, v} p q).symm
    (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))
    (site.{u, v} d).topology (site.{u, v} e).topology (site.{u, v} f).topology

/-- Composition on inverse images is the adjunction mate of directComp, so it retains
exactly the ordinary adjunction-unit normalization.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def pullComp {d e f : Diagram.{u}} (p : e ⟶ d) (q : f ⟶ e)
    (Λ : Type v) [CommRing Λ] : pull (q ≫ p) Λ ≅ pull p Λ ⋙ pull q Λ :=
  Adjunction.leftAdjointUniq
    ((baseChange.{u, v} (q ≫ p)).sheafAdjunctionContinuous _ _ _)
    ((((baseChange.{u, v} p).sheafAdjunctionContinuous _ _ _).comp
      ((baseChange.{u, v} q).sheafAdjunctionContinuous _ _ _)).ofNatIsoRight
        (directComp p q Λ))

/-- The same unit-normalized composition applied termwise and localized.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def starComp {d e f : Diagram.{u}} (p : e ⟶ d) (q : f ⟶ e)
    (Λ : Type v) [CommRing Λ] : star (q ≫ p) Λ ≅ star p Λ ⋙ star q Λ :=
  Functor.mapDerivedCategoryPlusNatIso (pullComp p q Λ) ≪≫
    Functor.mapDerivedCategoryPlusCompIso (pull p Λ) (pull q Λ)

/-- The canonical stage transition followed by its composite inverse-image identification.
It also applies to a projection to the limit and to any restriction of inverse systems.
Source: ILO XI §2.7 (*) (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def transition {d e f : Diagram.{u}} (p : e ⟶ d) (q : f ⟶ e) (r : f ⟶ d)
    (w : q ≫ p = r) (Λ : Type v) [CommRing Λ] (n : ℤ) :
    star p Λ ⋙ cohomology e Λ n ⟶ star r Λ ⋙ cohomology f Λ n :=
  Functor.whiskerLeft (star p Λ) (cohomologyPullback q Λ n) ≫
    Functor.whiskerRight
      ((starComp p q Λ).symm ≪≫ eqToIso (congrArg (fun a ↦ star a Λ) w)).hom
      (cohomology f Λ n)

/-- Composite cohomological pullback uses the composite-adjunction unit. In particular,
restriction along any commutative square of diagrams gives a commuting cohomology square.
Source: ILO XI §2.7 (*) (blueprint: lem-trf-oriented-derived-cohomology-continuity).
Proof: expand sectionPullbackApp. The composite adjunction's unit and the terminal
comparison are the composites of those for p and q. The defining three components of
baseChangeComp identify these maps with the map for r. The mate defining pullComp preserves
that unit. Apply the universal characterization of rightDerivedFunctorPlusBaseChange,
then take degree-n homology. This is the derived-composition normalization in the DAG. -/
theorem cohomologyPullback_comp {d e f : Diagram.{u}} (p : e ⟶ d) (q : f ⟶ e)
    (r : f ⟶ d) (w : q ≫ p = r) (Λ : Type v) [CommRing Λ] (n : ℤ) :
    cohomologyPullback p Λ n ≫ transition p q r w Λ n =
      cohomologyPullback r Λ n := by
  sorry

/-- Cofiltered-slice transition, functorial in the bounded-below complex.
Source: ILO XI §2.7 (*) (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def sliceTransition {I : Type u} [SmallCategory I] (D : I ⥤ Diagram.{u})
    {i₀ : I} {a b : Over i₀} (t : b ⟶ a) (Λ : Type v) [CommRing Λ] (n : ℤ) :=
  transition (D.map a.hom) (D.map t.left) (D.map b.hom)
    ((D.map_comp t.left a.hom).symm.trans (congrArg D.map (Over.w t))) Λ n

/-- The slice transitions satisfy the identity and composition laws.
Source: ILO XI §2.7 (*) (blueprint: lem-trf-oriented-derived-cohomology-continuity).
Proof: on sections, composition of inverse-image units is the composite-adjunction unit.
The terminal comparison respects composition. The three components defining baseChangeComp
satisfy the pullback associativity and unit identities. Taking adjunction mates gives the
same identities for pullComp. Apply the right-derived universal property and homology;
the equality of arrows in the slice identifies all composite inverse images. -/
theorem sliceTransition_laws {I : Type u} [SmallCategory I] (D : I ⥤ Diagram.{u})
    (i₀ : I) (Λ : Type v) [CommRing Λ] (n : ℤ) :
    (∀ a : Over i₀, sliceTransition D (𝟙 a) Λ n =
      𝟙 (star (D.map a.hom) Λ ⋙ cohomology (D.obj a.left) Λ n)) ∧
    (∀ {a b c : Over i₀} (t : b ⟶ a) (r : c ⟶ b),
      sliceTransition D (r ≫ t) Λ n =
        sliceTransition D t Λ n ≫ sliceTransition D r Λ n) := by
  sorry

/-- The actual filtered diagram of cohomology functors, indexed by the opposite slice.
Source: ILO XI §2.7; Stacks 09YP
(blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def cohomologyDiagram {I : Type u} [SmallCategory I] (D : I ⥤ Diagram.{u})
    (i₀ : I) (Λ : Type v) [CommRing Λ] (n : ℤ) :
    (Over i₀)ᵒᵖ ⥤ (DPlus (D.obj i₀) Λ ⥤
      ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ)) where
  obj a := star (D.map a.unop.hom) Λ ⋙ cohomology (D.obj a.unop.left) Λ n
  map t := sliceTransition D t.unop Λ n
  map_id a := (sliceTransition_laws D i₀ Λ n).1 a.unop
  map_comp t r := (sliceTransition_laws D i₀ Λ n).2 t.unop r.unop

/-- The projection-induced leg from one slice stage to the componentwise limit.
Source: ILO XI §2.7 (*) (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def limitLeg {I : Type u} [SmallCategory I] (D : I ⥤ Diagram.{u}) (c : Cone D)
    {i₀ : I} (a : Over i₀) (Λ : Type v) [CommRing Λ] (n : ℤ) :=
  transition (D.map a.hom) (c.π.app a.left) (c.π.app i₀) (c.w a.hom) Λ n

/-- Projection pullbacks form a cocone of natural transformations in K.
Source: ILO XI §2.7 (*) (blueprint: lem-trf-oriented-derived-cohomology-continuity).
Proof: the cone equation identifies projection followed by a transition with the earlier
projection. Composition of the ordinary adjunction units gives equality of section maps.
Derive that equality and take homology. The pullComp mate and the defining cone equations
are exactly the composition identifications used in limitLeg and sliceTransition. -/
theorem limitLeg_naturality {I : Type u} [SmallCategory I] (D : I ⥤ Diagram.{u})
    (c : Cone D) (i₀ : I) (Λ : Type v) [CommRing Λ] (n : ℤ)
    {a b : (Over i₀)ᵒᵖ} (t : a ⟶ b) :
    (cohomologyDiagram D i₀ Λ n).map t ≫ limitLeg D c b.unop Λ n =
      limitLeg D c a.unop Λ n := by
  sorry

/-- The canonical continuity cocone, with its original unit-defined pullback legs.
Its point is the cohomology of the actual componentwise limit.
Source: ILO XI §2.7 (*) (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def continuityCocone {I : Type u} [SmallCategory I] (D : I ⥤ Diagram.{u})
    (c : Cone D) (i₀ : I) (Λ : Type v) [CommRing Λ] (n : ℤ) :
    Cocone (cohomologyDiagram D i₀ Λ n) where
  pt := star (c.π.app i₀) Λ ⋙ cohomology c.pt Λ n
  ι :=
    { app := fun a ↦ limitLeg D c a.unop Λ n
      naturality := fun _ _ t ↦ (limitLeg_naturality D c i₀ Λ n t).trans
        (Category.comp_id _).symm }

/-- Restriction of a stage cohomology functor along a commutative square of scheme diagrams.
Both the stage inverse image and the distinguished-stage coefficient inverse image are
canonical; the final map is the unit-normalized starComp identification.
Source: ILO XI §2.7 (*) (blueprint: lem-trf-oriented-derived-cohomology-continuity). -/
def restriction {d d' e e' : Diagram.{u}} (p : e ⟶ d) (q : e' ⟶ d')
    (t : e' ⟶ e) (r : d' ⟶ d) (w : t ≫ p = q ≫ r)
    (Λ : Type v) [CommRing Λ] (n : ℤ) :
    star p Λ ⋙ cohomology e Λ n ⟶ star r Λ ⋙ star q Λ ⋙ cohomology e' Λ n :=
  transition p t (q ≫ r) w Λ n ≫
    Functor.whiskerRight (starComp r q Λ).hom (cohomology e' Λ n)

/-- Continuity commutes with restriction along morphisms of inverse systems. This is the
square on every canonical cocone leg: apply it to each stage arrow and its limit projection.
The systems may have different indices, since a reindexing functor simply supplies the
corresponding stage in the first system. Colimit universality turns these leg equations
into the commuting square for the canonical colimit comparisons, natural in K.

Source: ILO XI §2.7 (*) and the verification following (2.f)
(blueprint: lem-trf-oriented-derived-cohomology-continuity).

Proof: the two composites on sections are the same inverse-image unit followed by
restriction to the same terminal triple. The stage square and the two cone equations
identify their composite arrows. The mate definition of pullComp gives the associativity
coherence on coefficients. Derive the equality using the normalized right-derived units,
then take H^n. Thus the equality holds as natural transformations before taking the colimit;
its universal property proves the comparison square. No continuity assumption is needed
for this compatibility calculation itself. -/
theorem restriction_limitSquare {d d' e e' f f' : Diagram.{u}}
    (p : e ⟶ d) (q : e' ⟶ d') (t : e' ⟶ e) (r : d' ⟶ d)
    (w : t ≫ p = q ≫ r) (a : f ⟶ e) (b : f' ⟶ e') (l : f' ⟶ f)
    (_h : l ≫ a = b ≫ t) (c : f ⟶ d) (c' : f' ⟶ d')
    (hc : a ≫ p = c) (hc' : b ≫ q = c') (hl : l ≫ c = c' ≫ r)
    (Λ : Type v) [CommRing Λ] (n : ℤ) :
    transition p a c hc Λ n ≫ restriction c c' l r hl Λ n =
      restriction p q t r w Λ n ≫
        Functor.whiskerLeft (star r Λ) (transition q b c' hc' Λ n) := by
  sorry

/-- Continuity for every bounded-below constant-coefficient complex and every integer
cohomology degree. Being a colimit in the functor category retains naturality in K;
evaluation gives the displayed module-valued filtered-colimit comparison. No torsion,
constructibility or dimension hypothesis is imposed.

Source: ILO XI §§1.10(b), 2.5--2.7; Stacks 09YL and 09YP
(blueprint: lem-trf-oriented-derived-cohomology-continuity).

Proof (the eight steps of the DAG):
1. Replace I by I/i₀. The slice projection is initial by the cofiltered lifting criterion
(lem-weil-pbc-initial-functor-cofiltered-criterion), and preserves all three limits.
2. Use lem-trf-oriented-triple-limit-descent and lem-trf-qcqs-oriented-triple-presentation
for finite-cover triple sites, their colimiting object/arrow cocones, and the geometric
identification of their canonical maps. Apply lem-weil-pbc-colimit-of-sites.
3. For a sheaf in degree zero the inverse-image diagram on the limit is constant, by
composition of inverse images. Its colimit is that sheaf
(lem-weil-pbc-colimit-constant-connected-diagram). Apply
lem-weil-pbc-cohomology-colimit-of-sites at the final triple. The single identification
(lem-sp-derived-functor-single-identification) and negative vanishing
(lem-weil-pbc-derived-functor-negative-vanishing) give all integer degrees.
4. Module sheaves are Grothendieck (lem-weil-pbc-ring-sheaves-grothendieck), so use
K-injective resolutions (lem-sfb-grothendieck-k-injective). Derived sections and exact
inverse images are triangulated (lem-pc-right-derived-functor-triangulated and
lem-sf-exact-functor-derived-triangulated). The derived unit commutes with shifts
(lem-weil-pbc-derived-adjunction-shift); composition preserves its normalization
(lem-sfb-derived-composition-adjunction-normalization). Thus the pullback maps form
morphisms of long exact sequences (lem-weil-pbc-derived-cohomology-ladder).
5. Starting at a lower bound a, induct on finite upper truncations using the truncation
triangle (lem-weil-pbc-truncation-triangle). Its pieces are shifted sheaves. Exact
filtered colimits (lem-weil-pbc-filtered-colimit-abelian-groups-exact) and the five lemma
(lem-weil-pbc-five-lemma) propagate the comparison isomorphism.
6. Degree n only sees truncation at n (lem-weil-pbc-derived-functor-truncation-iso).
Use step 5 and the natural truncation square; below a both sides vanish. This avoids any
cohomological dimension bound or infinite spectral-sequence passage.
7. Forget the constant ring action. Exact inverse image commutes with this forgetting
(lem-pe-constant-left-module-inverse-image), and derived evaluation does too, preserving
the global pullback (lem-pe-left-module-derived-evaluation-forget). Filtered module
colimits have the underlying abelian-group colimits; a bijective linear map is invertible.
8. Every comparison is the original sectionPullback, derived by the universal right-derived
unit. Naturality of the section units and their composite-adjunction identity
(lem-weil-pbc-site-cohomology-pullback and
lem-sfb-derived-composition-adjunction-normalization) give naturality in K and restriction
of systems. Taking homology and the colimit preserves these squares. The functor-category
colimit and the restriction identity above retain precisely these canonical maps. -/
theorem orientedDerivedCohomology_continuity
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Diagram.{u})
    [∀ (i : I) (k : WalkingCospan), CompactSpace ((D.obj i).obj k)]
    [∀ (i : I) (k : WalkingCospan), QuasiSeparatedSpace ((D.obj i).obj k)]
    [∀ i : I, QuasiCompact ((D.obj i).map WalkingCospan.Hom.inl)]
    [∀ i : I, QuasiSeparated ((D.obj i).map WalkingCospan.Hom.inl)]
    [∀ i : I, QuasiCompact ((D.obj i).map WalkingCospan.Hom.inr)]
    [∀ i : I, QuasiSeparated ((D.obj i).map WalkingCospan.Hom.inr)]
    [∀ {i j : I} (a : i ⟶ j) (k : WalkingCospan), IsAffineHom ((D.map a).app k)]
    (c : Cone D) (_hc : IsLimit c) (i₀ : I) (Λ : Type v) [CommRing Λ] (n : ℤ) :
    Nonempty (IsColimit (continuityCocone D c i₀ Λ n)) := by
  sorry

end AlgebraicGeometry.OrientedDerivedContinuity
