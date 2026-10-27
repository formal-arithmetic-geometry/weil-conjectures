/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.SpaceModuleBaseChangeFlatProperSupport
public import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Sheaf.CategoryTheory.RingedSiteModules

/-! # The proper-support Quot presheaf

Source: Stacks Project, quot.tex, Tag 09TR, situation-quot; spaces-perfect.tex,
Tag 0CZI, lemma-module-support-proper-over-base
(blueprint: def-sfb-space-proper-quot-functor).

Test objects are schemes mapping to the algebraic space B. Values are actual quotients
of the type of admissible surjections by target isomorphisms. Transitions are tensor
pullback with the already normalized composition comparison on the source module.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {A B : AlgebraicSpace S}

/-- Schemes over B, retaining their maps as natural transformations.
Source: Stacks 09TR, test schemes (blueprint: def-sfb-space-proper-quot-functor). -/
abbrev ProperQuotTest (B : AlgebraicSpace S) := CostructuredArrow yoneda B.obj.obj

/-- The test scheme's specified map to B, as an algebraic-space map.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def properQuotTestMap (T : ProperQuotTest B) : schemeSpace T.left ⟶ B :=
  ObjectProperty.homMk ⟨T.hom⟩

/-- The sheaf fibre product A_T = A ×_B T, with no arbitrary model chosen.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def properQuotFibre (a : A ⟶ B) (T : ProperQuotTest B) : AlgebraicSpace S :=
  ⟨Limits.pullback a.hom (properQuotTestMap T).hom,
    (fibreProduct_isAlgebraicSpace A (schemeSpace T.left) B a (properQuotTestMap T)).1⟩

/-- The projection used to tensor-pull F back to A_T.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def properQuotFst (a : A ⟶ B) (T : ProperQuotTest B) : properQuotFibre a T ⟶ A :=
  ObjectProperty.homMk (Limits.pullback.fst a.hom (properQuotTestMap T).hom)

/-- The structural projection A_T → T.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def properQuotSnd (a : A ⟶ B) (T : ProperQuotTest B) :
    properQuotFibre a T ⟶ schemeSpace T.left :=
  ObjectProperty.homMk (Limits.pullback.snd a.hom (properQuotTestMap T).hom)

/-- Finite presentation is local finite presentation, quasi-compactness, and
quasi-compactness of the diagonal, exactly as stipulated in the node.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def ProperQuotFinitePresentation (a : A ⟶ B) : Prop :=
  MapIsLocallyOfFinitePresentation a ∧ MapIsQuasiCompact a.hom.hom ∧
    MapIsQuasiCompact (Limits.pullback.diagonal a.hom.hom)

/-- An admissible quotient before passing to isomorphism classes. Surjectivity is
sheaf surjectivity (Epi), not surjectivity on every set of sections. Relative flatness
is the recorded scheme predicate on every Zariski restriction to an etale chart.
Source: Stacks 09TR and 0CZI(3)
(blueprint: def-sfb-space-proper-quot-functor). -/
structure ProperQuotient (a : A ⟶ B) (F : A.Modules) (T : ProperQuotTest B) where
  /-- Target module on the small etale ringed site of A_T. -/
  target : (properQuotFibre a T).Modules
  /-- The actual quotient map from the specified tensor pullback F_T. -/
  quotient : (moduleTensorPullback (properQuotFst a T)).obj F ⟶ target
  /-- Surjective as a morphism of module sheaves. -/
  surjective : Epi quotient
  /-- Quasi-coherent. -/
  quasicoherent : target.IsQuasicoherent
  /-- Locally a cokernel of a map between finite free module sheaves. -/
  finitePresentation : target.IsFinitePresentation
  /-- Flat over the test scheme, checked on every etale scheme chart. -/
  flat : ∀ U : (properQuotFibre a T).EtaleSite,
    ((schemeRestriction (properQuotFibre a T) U).obj target).IsFlatOver
      (yoneda.preimage (U.obj.hom ≫ (properQuotSnd a T).hom.hom)).left
  /-- A closed proper carrier with a finite type quasi-coherent module realizing target. -/
  properSupport : ∃ (Z : AlgebraicSpace S) (i : Z ⟶ properQuotFibre a T),
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
    MapIsProper (i ≫ properQuotSnd a T) ∧ ∃ G : Z.Modules,
      G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ target)

/-- Two surjections are identified exactly by an intertwining target isomorphism.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def ProperQuotientRel (a : A ⟶ B) (F : A.Modules) (T : ProperQuotTest B)
    (q r : ProperQuotient a F T) : Prop :=
  ∃ e : q.target ≅ r.target, q.quotient ≫ e.hom = r.quotient

/-- Values of the Quot presheaf: isomorphism classes of the admissible surjections.
The relation is already an equivalence, by identity, inverse and composition of isos.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def ProperQuotClasses (a : A ⟶ B) (F : A.Modules) (T : ProperQuotTest B) :=
  Quot (ProperQuotientRel a F T)

/-- Compatibility of the test-scheme map with the two structural maps to B.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor).
Proof: this is precisely the commuting triangle in the costructured arrow category,
viewed as an equality of sheaf morphisms; the two full embeddings are faithful. -/
theorem properQuotTestMap_w {T' T : ProperQuotTest B} (h : T' ⟶ T) :
    ((Scheme.fppfTopology.over S).yoneda.map h.left) ≫ (properQuotTestMap T).hom =
      (properQuotTestMap T').hom := by
  sorry

/-- The map A_T' → A_T induced by the identity on A and the given map T' → T.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def properQuotFibreMap (a : A ⟶ B) {T' T : ProperQuotTest B} (h : T' ⟶ T) :
    properQuotFibre a T' ⟶ properQuotFibre a T :=
  ObjectProperty.homMk (Limits.pullback.map a.hom (properQuotTestMap T').hom
    a.hom (properQuotTestMap T).hom (𝟙 A.obj)
    ((Scheme.fppfTopology.over S).yoneda.map h.left) (𝟙 B.obj)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (properQuotTestMap_w h).symm))

/-- The induced fibre map commutes with the projection to A.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor).
Proof: apply the first projection identity of pullback.map; its A-component is identity. -/
theorem properQuotFibreMap_fst (a : A ⟶ B) {T' T : ProperQuotTest B} (h : T' ⟶ T) :
    properQuotFibreMap a h ≫ properQuotFst a T = properQuotFst a T' := by
  sorry

/-- Canonical identification (F_T)_T' ≅ F_T', using the existing tensor associator.
Source: Stacks 09TR, tensor pullback transition
(blueprint: def-sfb-space-proper-quot-functor). -/
def properQuotSourceIso (a : A ⟶ B) (F : A.Modules)
    {T' T : ProperQuotTest B} (h : T' ⟶ T) :
    (moduleTensorPullback (properQuotFibreMap a h)).obj
        ((moduleTensorPullback (properQuotFst a T)).obj F) ≅
      (moduleTensorPullback (properQuotFst a T')).obj F :=
  (moduleTensorComposition (properQuotFibreMap a h) (properQuotFst a T)).app F ≪≫
    eqToIso (congrArg (fun p ↦ (moduleTensorPullback p).obj F) (properQuotFibreMap_fst a h))

/-- The pulled-back surjection, with precisely F_T' as its source.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def properQuotPullbackArrow (a : A ⟶ B) (F : A.Modules)
    {T' T : ProperQuotTest B} (h : T' ⟶ T) (q : ProperQuotient a F T) :
    (moduleTensorPullback (properQuotFst a T')).obj F ⟶
      (moduleTensorPullback (properQuotFibreMap a h)).obj q.target :=
  (properQuotSourceIso a F h).inv ≫
    (moduleTensorPullback (properQuotFibreMap a h)).map q.quotient

/-- All admissibility properties of the actual pulled target and quotient arrow.
Source: Stacks 09TR, 03DO, 05VW, 0CZI and 0CZJ
(blueprint: def-sfb-space-proper-quot-functor).
Proof: choose surjective etale charts V of B and U of A ×_B V. Finite presentation
of a makes U → V locally finitely presented, hence locally of finite type. Pull
these charts back to T; locallyOfFiniteType_isStableUnderBaseChange and
local_properties_chart_test show that A_T → T is locally of finite type.
The square A_T' → A_T over T' → T is cartesian by pullback pasting.
Apply moduleTensorPullback_flat_properSupport_baseChange to this square and q's
four target properties. Its output gives the four target clauses below.
Tensor pullback is a left adjoint, hence preserves cokernels and epimorphisms in
these module-sheaf categories. Precomposition with the canonical source iso preserves
surjectivity, giving the first clause. No flatness of T' → T is used. -/
theorem properQuotPullback_properties (a : A ⟶ B) (ha : ProperQuotFinitePresentation a)
    (F : A.Modules) {T' T : ProperQuotTest B} (h : T' ⟶ T)
    (q : ProperQuotient a F T) :
    Epi (properQuotPullbackArrow a F h q) ∧
    ((moduleTensorPullback (properQuotFibreMap a h)).obj q.target).IsQuasicoherent ∧
    ((moduleTensorPullback (properQuotFibreMap a h)).obj q.target).IsFinitePresentation ∧
    (∀ U : (properQuotFibre a T').EtaleSite,
      ((schemeRestriction (properQuotFibre a T') U).obj
        ((moduleTensorPullback (properQuotFibreMap a h)).obj q.target)).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫ (properQuotSnd a T').hom.hom)).left) ∧
    (∃ (Z : AlgebraicSpace S) (i : Z ⟶ properQuotFibre a T'),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
      MapIsProper (i ≫ properQuotSnd a T') ∧ ∃ G : Z.Modules,
        G.IsQuasicoherent ∧ G.IsFiniteType ∧
          Nonempty ((moduleDirectImage i).obj G ≅
            (moduleTensorPullback (properQuotFibreMap a h)).obj q.target)) := by
  sorry

/-- Tensor pullback of an admissible quotient, with its preserved target conditions.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def properQuotPullback (a : A ⟶ B) (ha : ProperQuotFinitePresentation a) (F : A.Modules)
    {T' T : ProperQuotTest B} (h : T' ⟶ T) (q : ProperQuotient a F T) :
    ProperQuotient a F T' where
  target := (moduleTensorPullback (properQuotFibreMap a h)).obj q.target
  quotient := properQuotPullbackArrow a F h q
  surjective := (properQuotPullback_properties a ha F h q).1
  quasicoherent := (properQuotPullback_properties a ha F h q).2.1
  finitePresentation := (properQuotPullback_properties a ha F h q).2.2.1
  flat := (properQuotPullback_properties a ha F h q).2.2.2.1
  properSupport := (properQuotPullback_properties a ha F h q).2.2.2.2

/-- Tensor pullback respects exactly the target-isomorphism relation.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor).
Proof: apply the pullback functor to the intertwining isomorphism. Functoriality
and naturality of the canonical source comparison give the required intertwining
identity for the pulled surjections. -/
theorem properQuotPullback_rel (a : A ⟶ B) (ha : ProperQuotFinitePresentation a)
    (F : A.Modules) {T' T : ProperQuotTest B} (h : T' ⟶ T)
    (q r : ProperQuotient a F T) (e : ProperQuotientRel a F T q r) :
    ProperQuotientRel a F T' (properQuotPullback a ha F h q)
      (properQuotPullback a ha F h r) := by
  sorry

/-- Transition on the set of isomorphism classes, induced by actual tensor pullback.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor). -/
def properQuotMap (a : A ⟶ B) (ha : ProperQuotFinitePresentation a) (F : A.Modules)
    {T' T : ProperQuotTest B} (h : T' ⟶ T) :
    ProperQuotClasses a F T → ProperQuotClasses a F T' :=
  Quot.map (properQuotPullback a ha F h) (properQuotPullback_rel a ha F h)

/-- Identity transitions act as identity on isomorphism classes.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor).
Proof: the fibre map induced by identity is identity by the two pullback projections.
The canonical tensor unit isomorphism identifies the pulled target with the original
one and intertwines their surjections. Quot.sound therefore identifies their classes;
quotient induction gives equality of the functions. -/
theorem properQuotMap_id (a : A ⟶ B) (ha : ProperQuotFinitePresentation a)
    (F : A.Modules) (T : ProperQuotTest B) :
    properQuotMap a ha F (𝟙 T) = id := by
  sorry

/-- Composition transitions act by successive tensor pullback on isomorphism classes.
Source: Stacks 09TR (blueprint: def-sfb-space-proper-quot-functor).
Proof: the induced fibre maps compose by uniqueness of pullback lifts. The existing
local-tensor-normalized associator identifies the two pulled targets. Its naturality
and tensor associativity show that this isomorphism intertwines the quotient arrows,
including the source identifications. Quot.sound and quotient induction prove equality. -/
theorem properQuotMap_comp (a : A ⟶ B) (ha : ProperQuotFinitePresentation a)
    (F : A.Modules) {T'' T' T : ProperQuotTest B} (h : T'' ⟶ T') (k : T' ⟶ T) :
    properQuotMap a ha F (h ≫ k) = properQuotMap a ha F h ∘ properQuotMap a ha F k := by
  sorry

/-- The proper-support Quot presheaf of a quasi-coherent module F along a finitely
presented algebraic-space map a. Every value and transition is explicitly constructed.
Source: Stacks Project, Tag 09TR, situation-quot, with Tag 0CZI(3)
(blueprint: def-sfb-space-proper-quot-functor). -/
def properQuotFunctor (a : A ⟶ B) (ha : ProperQuotFinitePresentation a) (F : A.QCoh) :
    (ProperQuotTest B)ᵒᵖ ⥤ Type (u + 1) where
  obj T := ProperQuotClasses a F.obj T.unop
  map h := TypeCat.ofHom (properQuotMap a ha F.obj h.unop)
  map_id T := congrArg TypeCat.ofHom (properQuotMap_id a ha F.obj T.unop)
  map_comp h k := congrArg TypeCat.ofHom (properQuotMap_comp a ha F.obj k.unop h.unop)

end AlgebraicGeometry.AlgebraicSpace
