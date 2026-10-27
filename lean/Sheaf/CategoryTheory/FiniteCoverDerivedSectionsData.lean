module

public import WeilConjectures.CategoryTheory.ColimitSites
public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Resolution presentations for finite-cover continuity

Source: Stacks Project, Sites 09YL and Cohomology on Sites 0EXZ, 09YP;
Derived Categories 013K, 013P, 013S, 015E
(blueprint: def-per-finite-cover-derived-sections-data).

All arrows in a presentation are normalized on sections. In particular the cocone
into the receiving injective resolution is the actual adjunction-unit and
coprojection map, rather than an unspecified isomorphism in the derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory.FiniteCoverDerivedSections

/-- A finite-cover diagram and its colimit site. The filtered index is the opposite
of the cofiltered index in Stacks. Finite composition and base change, rather than
unrestricted repeated-index axioms, are used.
Source: Stacks, Sites 0A34, 09YL, 0A35
(blueprint: def-per-finite-cover-derived-sections-data). -/
structure Sites where
  Index : Type u
  indexCategory : SmallCategory Index
  filtered : IsFiltered Index
  diagram : Index ⥤ Cat.{u, u}
  covers : ∀ i : Index, Precoverage (diagram.obj i)
  isos : ∀ i : Index, (covers i).HasIsos
  composition : ∀ i : Index, (covers i).IsStableUnderFiniteComposition
  baseChange : ∀ i : Index, (covers i).IsStableUnderFiniteBaseChange
  pullbacks : ∀ i : Index, (covers i).HasPullbacks
  finite : ∀ (i : Index) (X : diagram.obj i) (R : Presieve X),
    R ∈ covers i X → Finite R.uncurry
  finiteLimits : ∀ i : Index, HasFiniteLimits (diagram.obj i)
  preserves : ∀ {i j : Index} (a : i ⟶ j),
    PreservesFiniteLimits (diagram.map a).toFunctor
  covering : ∀ {i j : Index} (a : i ⟶ j) (X : diagram.obj i) (R : Presieve X),
    R ∈ covers i X → R.map (diagram.map a).toFunctor ∈
      covers j ((diagram.map a).toFunctor.obj X)
  continuous : ∀ {i j : Index} (a : i ⟶ j),
    (diagram.map a).toFunctor.IsContinuous (covers i).toGrothendieck
      (covers j).toGrothendieck
  cocone : Cocone diagram
  objects : IsColimit (Cat.objects.mapCocone cocone)
  arrows : IsColimit (Cat.arrows.mapCocone cocone)
  limitCovers : Precoverage cocone.pt
  limitIsos : limitCovers.HasIsos
  limitComposition : limitCovers.IsStableUnderFiniteComposition
  limitBaseChange : limitCovers.IsStableUnderFiniteBaseChange
  limitPullbacks : limitCovers.HasPullbacks
  limitFiniteLimits : HasFiniteLimits cocone.pt
  limitCovering : ∀ (Y : cocone.pt) (R : Presieve Y), R ∈ limitCovers Y ↔
    ∃ (i : Index) (X : diagram.obj i) (S : Presieve X)
      (h : (cocone.ι.app i).toFunctor.obj X = Y),
      S ∈ covers i X ∧ h ▸ S.map (cocone.ι.app i).toFunctor = R
  projectionPreserves : ∀ i : Index, PreservesFiniteLimits (cocone.ι.app i).toFunctor
  projectionContinuous : ∀ i : Index,
    (cocone.ι.app i).toFunctor.IsContinuous (covers i).toGrothendieck
      limitCovers.toGrothendieck

attribute [instance] Sites.indexCategory Sites.filtered Sites.isos Sites.composition
  Sites.baseChange Sites.pullbacks Sites.finiteLimits Sites.preserves Sites.continuous
  Sites.limitIsos Sites.limitComposition Sites.limitBaseChange Sites.limitPullbacks
  Sites.limitFiniteLimits Sites.projectionPreserves Sites.projectionContinuous

/-- Precomposition is additive, with sectionwise addition on sheaf maps.
Source: Stacks, Modules on Sites 03DC
(blueprint: def-per-finite-cover-derived-sections-data). -/
instance pushforwardAdditive {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
    [f.IsContinuous J K] : (f.sheafPushforwardContinuous AddCommGrpCat.{u} J K).Additive
    where
  map_add := rfl

/-- The actual left adjoint is additive, as the left adjoint of additive precomposition.
Source: Stacks, Modules on Sites 04JC
(blueprint: def-per-finite-cover-derived-sections-data). -/
instance pullbackAdditive {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
    [f.IsContinuous J K] : (sheafPullback f AddCommGrpCat.{u} J K).Additive :=
  (sheafAdjunctionContinuous f AddCommGrpCat.{u} J K).left_adjoint_additive

/-- Sections at an object are additive.
Source: Stacks, Cohomology on Sites 01FT
(blueprint: def-per-finite-cover-derived-sections-data). -/
instance evaluationAdditive {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (X : C) :
    ((sheafSections J AddCommGrpCat.{u}).obj (op X)).Additive :=
  inferInstanceAs ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op X)).Additive)

/-- The category of abelian sheaves at a stage.
Source: Stacks 0EXZ (blueprint: def-per-finite-cover-derived-sections-data). -/
abbrev Sites.Abelian (S : Sites.{u}) (i : S.Index) :=
  Sheaf (S.covers i).toGrothendieck AddCommGrpCat.{u}

/-- The abelian sheaves on the actual colimit site.
Source: Stacks 09YP (blueprint: def-per-finite-cover-derived-sections-data). -/
abbrev Sites.LimitAbelian (S : Sites.{u}) :=
  Sheaf S.limitCovers.toGrothendieck AddCommGrpCat.{u}

/-- Direct image on complexes along a transition, computed by precomposition.
Source: Stacks 0EXZ (blueprint: def-per-finite-cover-derived-sections-data). -/
abbrev Sites.push (S : Sites.{u}) {i j : S.Index} (a : i ⟶ j) :=
  ((S.diagram.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
    (S.covers i).toGrothendieck (S.covers j).toGrothendieck).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- Direct image on complexes along the projection from the colimit site.
Source: Stacks 0A35 (blueprint: def-per-finite-cover-derived-sections-data). -/
abbrev Sites.projectionPush (S : Sites.{u}) (i : S.Index) :=
  ((S.cocone.ι.app i).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
    (S.covers i).toGrothendieck S.limitCovers.toGrothendieck).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- Inverse image on complexes along a projection, using Mathlib's actual left adjoint.
Source: Stacks 0A35, 04JC (blueprint: def-per-finite-cover-derived-sections-data). -/
abbrev Sites.projectionPull (S : Sites.{u}) (i : S.Index) :=
  (sheafPullback (S.cocone.ι.app i).toFunctor AddCommGrpCat.{u}
    (S.covers i).toGrothendieck S.limitCovers.toGrothendieck).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- Global sections computed at the terminal site object, term by term.
Source: Stacks 01FT (blueprint: def-per-finite-cover-derived-sections-data). -/
abbrev Sites.sections (S : Sites.{u}) (i : S.Index) :=
  ((sheafSections (S.covers i).toGrothendieck AddCommGrpCat.{u}).obj
    (op (⊤_ (S.diagram.obj i)))).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- Global sections on the colimit site, term by term.
Source: Stacks 01FT (blueprint: def-per-finite-cover-derived-sections-data). -/
abbrev Sites.limitSections (S : Sites.{u}) :=
  ((sheafSections S.limitCovers.toGrothendieck AddCommGrpCat.{u}).obj
    (op (⊤_ S.cocone.pt))).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- A complex system, with adjoint transition maps. Heterogeneous equalities merely
transport along the strict Cat diagram's identity and composition equations.
Source: Stacks 0EXZ, applied degreewise
(blueprint: def-per-finite-cover-derived-sections-data). -/
structure System (S : Sites.{u}) where
  complex : ∀ i : S.Index, CochainComplex (S.Abelian i) ℤ
  transition : ∀ {i j : S.Index} (a : i ⟶ j), complex i ⟶ (S.push a).obj (complex j)
  identity : ∀ i : S.Index, HEq (transition (𝟙 i)) (𝟙 (complex i))
  composition : ∀ {i j k : S.Index} (a : i ⟶ j) (b : j ⟶ k),
    HEq (transition (a ≫ b)) (transition a ≫ (S.push a).map (transition b))

/-- A map of coefficient systems before taking any resolution.
Source: Stacks 0EXZ (blueprint: def-per-finite-cover-derived-sections-data). -/
structure System.Map {S : Sites.{u}} (K L : System S) where
  map : ∀ i : S.Index, K.complex i ⟶ L.complex i
  comm : ∀ {i j : S.Index} (a : i ⟶ j),
    map i ≫ L.transition a = K.transition a ≫ (S.push a).map (map j)

/-- The actual diagram on the limit site and its colimit. Transposing a transition
of `diagram` gives exactly the system transition followed by the projection unit;
thus this is the colimit of the inverse images, with their actual coprojections.
Source: Stacks 0A35, 09YP
(blueprint: def-per-finite-cover-derived-sections-data). -/
structure System.Colimit {S : Sites.{u}} (K : System S) where
  diagram : S.Index ⥤ CochainComplex S.LimitAbelian ℤ
  iso : ∀ i : S.Index, (S.projectionPull i).obj (K.complex i) ≅ diagram.obj i
  transition : ∀ {i j : S.Index} (a : i ⟶ j) (n : ℤ),
    HEq
      ((sheafAdjunctionContinuous (S.cocone.ι.app i).toFunctor AddCommGrpCat.{u}
        (S.covers i).toGrothendieck S.limitCovers.toGrothendieck).homEquiv
          ((K.complex i).X n) ((diagram.obj j).X n)
          ((iso i).hom.f n ≫ (diagram.map a).f n))
      ((K.transition a).f n ≫
        ((S.diagram.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (S.covers i).toGrothendieck (S.covers j).toGrothendieck).map
            (((sheafAdjunctionContinuous (S.cocone.ι.app j).toFunctor AddCommGrpCat.{u}
              (S.covers j).toGrothendieck S.limitCovers.toGrothendieck).unit.app
                ((K.complex j).X n)) ≫
              ((S.cocone.ι.app j).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                (S.covers j).toGrothendieck S.limitCovers.toGrothendieck).map
                  ((iso j).hom.f n)))
  cocone : Cocone diagram
  isColimit : IsColimit cocone

/-- A map from a system to a complex on the limit site, in adjoint form.
Source: Stacks 0EXZ (blueprint: def-per-finite-cover-derived-sections-data). -/
structure System.Leg {S : Sites.{u}} (K : System S)
    (L : CochainComplex S.LimitAbelian ℤ) where
  map : ∀ i : S.Index, K.complex i ⟶ (S.projectionPush i).obj L
  comm : ∀ {i j : S.Index} (a : i ⟶ j),
    HEq (map i) (K.transition a ≫ (S.push a).map (map j))

/-- Normalization of an adjoint leg by the actual colimit coprojection.
Source: Stacks 09YP (blueprint: def-per-finite-cover-derived-sections-data). -/
def System.Colimit.IsCoprojection {S : Sites.{u}} {K : System S} (C : K.Colimit)
    (l : K.Leg C.cocone.pt) : Prop :=
  ∀ (i : S.Index) (n : ℤ), (l.map i).f n =
    (sheafAdjunctionContinuous (S.cocone.ι.app i).toFunctor AddCommGrpCat.{u}
      (S.covers i).toGrothendieck S.limitCovers.toGrothendieck).homEquiv
        ((K.complex i).X n) (C.cocone.pt.X n)
        ((C.iso i).hom.f n ≫ (C.cocone.ι.app i).f n)

/-- An adjoint map's section map is normalized by restricting along the unique map
from the image of the source terminal object to the target terminal object. This
formula is the adjunction unit followed by the coefficient map, on global sections.
Source: Stacks 08J6 (blueprint: def-per-finite-cover-derived-sections-data). -/
def IsSectionMap {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasTerminal C] [HasTerminal D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
    [f.IsContinuous J K]
    (A : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ)
    (B : CochainComplex (Sheaf K AddCommGrpCat.{u}) ℤ)
    (a : A ⟶ ((f.sheafPushforwardContinuous AddCommGrpCat.{u} J K).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj B)
    (s : (((sheafSections J AddCommGrpCat.{u}).obj (op (⊤_ C))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ⟶
      (((sheafSections K AddCommGrpCat.{u}).obj (op (⊤_ D))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj B) : Prop :=
  ∀ n : ℤ, s.f n ≫ (B.X n).obj.map (terminal.from (f.obj (⊤_ C))).op =
    (a.f n).hom.app (op (⊤_ C))

/-- The actual diagram of global-section complexes of a system.
Source: Stacks 09YP (blueprint: def-per-finite-cover-derived-sections-data). -/
structure System.Sections {S : Sites.{u}} (K : System S) where
  diagram : S.Index ⥤ CochainComplex AddCommGrpCat.{u} ℤ
  iso : ∀ i : S.Index, diagram.obj i ≅ (S.sections i).obj (K.complex i)
  transition : ∀ {i j : S.Index} (a : i ⟶ j),
    IsSectionMap (S.covers i).toGrothendieck (S.covers j).toGrothendieck
      (S.diagram.map a).toFunctor (K.complex i) (K.complex j) (K.transition a)
      ((iso i).inv ≫ diagram.map a ≫ (iso j).hom)

/-- The receiving cocone into sections of a complex on the limit site.
Source: Stacks 09YP, 013P (blueprint: def-per-finite-cover-derived-sections-data). -/
structure System.Sections.Cocone {S : Sites.{u}} {K : System S} (A : K.Sections)
    (R : CochainComplex S.LimitAbelian ℤ) (l : K.Leg R) where
  cocone : Limits.Cocone A.diagram
  iso : cocone.pt ≅ (S.limitSections).obj R
  leg : ∀ i : S.Index,
    @IsSectionMap _ _ _ _ _ _ (S.covers i).toGrothendieck S.limitCovers.toGrothendieck
      (S.cocone.ι.app i).toFunctor (S.projectionContinuous i) (K.complex i) R (l.map i)
      ((A.iso i).inv ≫ cocone.ι.app i ≫ iso.hom)

/-- A compatible monomorphic injective resolution and its receiving limit resolution.
The source is the termwise colimit of the resolved section complexes. No object
or arrow is chosen from an unproved existence claim.
Source: Stacks 0EXZ, 013K, 013P, 09YP
(blueprint: def-per-finite-cover-derived-sections-data). -/
structure Model {S : Sites.{u}} (K : System S) (C : K.Colimit) (b : ℤ) where
  resolved : System S
  augmentation : K.Map resolved
  mono : ∀ (i : S.Index) (n : ℤ), Mono ((augmentation.map i).f n)
  quasiIso : ∀ i : S.Index, QuasiIso (augmentation.map i)
  kInjective : ∀ i : S.Index, (resolved.complex i).IsKInjective
  below : ∀ (i : S.Index) (n : ℤ), n < b → IsZero ((resolved.complex i).X n)
  injective : ∀ (i : S.Index) (n : ℤ), Injective ((resolved.complex i).X n)
  receiver : CochainComplex S.LimitAbelian ℤ
  receiverMap : C.cocone.pt ⟶ receiver
  receiverMono : ∀ n : ℤ, Mono (receiverMap.f n)
  receiverQuasiIso : QuasiIso receiverMap
  receiverKInjective : receiver.IsKInjective
  receiverBelow : ∀ n : ℤ, n < b → IsZero (receiver.X n)
  receiverInjective : ∀ n : ℤ, Injective (receiver.X n)
  coprojection : K.Leg C.cocone.pt
  isCoprojection : C.IsCoprojection coprojection
  lift : resolved.Leg receiver
  extension : ∀ i : S.Index,
    augmentation.map i ≫ lift.map i =
      coprojection.map i ≫ (S.projectionPush i).map receiverMap
  sections : resolved.Sections
  sectionCocone : sections.Cocone receiver lift

/-- The concrete chain map representing derived continuity, using colimit.desc on
the normalized resolution cocone. Its source and target are resolution models
of the two derived objects in the continuity statement.
Source: Stacks 09YP, 015E (blueprint: def-per-finite-cover-derived-sections-data). -/
def Model.comparison {S : Sites.{u}} {K : System S} {C : K.Colimit} {b : ℤ}
    (M : Model K C b) : colimit M.sections.diagram ⟶ (S.limitSections).obj M.receiver :=
  colimit.desc M.sections.diagram M.sectionCocone.cocone ≫ M.sectionCocone.iso.hom


/-- The stage resolution, using the shared K-injective bridge's definition.
Source: Stacks 070J (blueprint: def-per-finite-cover-derived-sections-data). -/
def Model.stageResolution {S : Sites.{u}} {K : System S} {C : K.Colimit} {b : ℤ}
    (M : Model K C b) (i : S.Index) :
    CochainComplex.KInjectiveResolutionChoice (K.complex i) where
  complex := M.resolved.complex i
  map := M.augmentation.map i
  quasiIso := M.quasiIso i
  isKInjective := M.kInjective i

/-- The receiving resolution, in the shared K-injective bridge.
Source: Stacks 070J (blueprint: def-per-finite-cover-derived-sections-data). -/
def Model.limitResolution {S : Sites.{u}} {K : System S} {C : K.Colimit} {b : ℤ}
    (M : Model K C b) : CochainComplex.KInjectiveResolutionChoice C.cocone.pt where
  complex := M.receiver
  map := M.receiverMap
  quasiIso := M.receiverQuasiIso
  isKInjective := M.receiverKInjective

/-- The adjoint of the actual coprojection in degree n.
Source: Stacks 09YP (blueprint: def-per-finite-cover-derived-sections-data). -/
def System.Colimit.legAt {S : Sites.{u}} {K : System S} (C : K.Colimit)
    (i : S.Index) (n : ℤ) :=
  (sheafAdjunctionContinuous (S.cocone.ι.app i).toFunctor AddCommGrpCat.{u}
    (S.covers i).toGrothendieck S.limitCovers.toGrothendieck).homEquiv
      ((K.complex i).X n) (C.cocone.pt.X n)
      ((C.iso i).hom.f n ≫ (C.cocone.ι.app i).f n)

/-- A finite-limit and cover preserving change between two diagrams, allowing a
change of index. Squares are natural isomorphisms; strict squares are not required.
Source: Stacks 08J6, 09YP
(blueprint: def-per-finite-cover-derived-sections-data). -/
structure SiteChange (S T : Sites.{u}) where
  index : S.Index ⥤ T.Index
  stage : ∀ i : S.Index, S.diagram.obj i ⥤ T.diagram.obj (index.obj i)
  stagePreserves : ∀ i : S.Index, PreservesFiniteLimits (stage i)
  stageCovering : ∀ (i : S.Index) (X : S.diagram.obj i) (R : Presieve X),
    R ∈ S.covers i X → R.map (stage i) ∈ T.covers (index.obj i) ((stage i).obj X)
  stageContinuous : ∀ i : S.Index, (stage i).IsContinuous
    (S.covers i).toGrothendieck (T.covers (index.obj i)).toGrothendieck
  limit : S.cocone.pt ⥤ T.cocone.pt
  limitPreserves : PreservesFiniteLimits limit
  limitCovering : ∀ (X : S.cocone.pt) (R : Presieve X),
    R ∈ S.limitCovers X → R.map limit ∈ T.limitCovers (limit.obj X)
  limitContinuous : limit.IsContinuous S.limitCovers.toGrothendieck
    T.limitCovers.toGrothendieck
  square : ∀ {i j : S.Index} (a : i ⟶ j),
    (S.diagram.map a).toFunctor ⋙ stage j ≅
      stage i ⋙ (T.diagram.map (index.map a)).toFunctor
  projection : ∀ i : S.Index, (S.cocone.ι.app i).toFunctor ⋙ limit ≅
    stage i ⋙ (T.cocone.ι.app (index.obj i)).toFunctor
  identity : ∀ (i : S.Index) (X : S.diagram.obj i),
    HEq ((square (𝟙 i)).hom.app X) (𝟙 ((stage i).obj X))
  composition : ∀ (i j k : S.Index) (a : i ⟶ j) (b : j ⟶ k) (X : S.diagram.obj i),
    HEq ((square (a ≫ b)).hom.app X)
      ((square b).hom.app ((S.diagram.map a).toFunctor.obj X) ≫
        (T.diagram.map (index.map b)).toFunctor.map ((square a).hom.app X))
  projectionCoherence : ∀ (i j : S.Index) (a : i ⟶ j) (X : S.diagram.obj i),
    HEq ((projection i).hom.app X)
      ((projection j).hom.app ((S.diagram.map a).toFunctor.obj X) ≫
        (T.cocone.ι.app (index.obj j)).toFunctor.map ((square a).hom.app X))

attribute [instance] SiteChange.stagePreserves SiteChange.stageContinuous
  SiteChange.limitPreserves SiteChange.limitContinuous

/-- Precomposition on complexes for a connecting site functor.
Source: Stacks 08J6 (blueprint: def-per-finite-cover-derived-sections-data). -/
abbrev SiteChange.push {S T : Sites.{u}} (U : SiteChange S T) (i : S.Index) :=
  ((U.stage i).sheafPushforwardContinuous AddCommGrpCat.{u}
    (S.covers i).toGrothendieck (T.covers (U.index.obj i)).toGrothendieck).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- Precomposition at the limit for a connecting site functor.
Source: Stacks 08J6 (blueprint: def-per-finite-cover-derived-sections-data). -/
abbrev SiteChange.limitPush {S T : Sites.{u}} (U : SiteChange S T) :=
  (U.limit.sheafPushforwardContinuous AddCommGrpCat.{u}
    S.limitCovers.toGrothendieck T.limitCovers.toGrothendieck).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- The coefficient square, written on sections to include the specified site square.
Source: Stacks 08J6, 0EXZ (blueprint: def-per-finite-cover-derived-sections-data). -/
def Compatible {S T : Sites.{u}} (U : SiteChange S T) (K : System S) (L : System T)
    (h : ∀ i : S.Index, K.complex i ⟶ (U.push i).obj (L.complex (U.index.obj i))) :
    Prop :=
  ∀ (i j : S.Index) (a : i ⟶ j) (n : ℤ) (X : S.diagram.obj i),
    ((h i).f n).hom.app (op X) ≫
      ((L.transition (U.index.map a)).f n).hom.app (op ((U.stage i).obj X)) ≫
      ((L.complex (U.index.obj j)).X n).obj.map ((U.square a).hom.app X).op =
    ((K.transition a).f n).hom.app (op X) ≫
      ((h j).f n).hom.app (op ((S.diagram.map a).toFunctor.obj X))

/-- A map of coefficient systems, including the induced map on their actual colimits.
The last equation specifies that map on every coprojection; it is not arbitrary.
Source: Stacks 08J6, 09YP
(blueprint: def-per-finite-cover-derived-sections-data). -/
structure Change {S T : Sites.{u}} (U : SiteChange S T) (K : System S) (C : K.Colimit)
    (L : System T) (D : L.Colimit) where
  stage : ∀ i : S.Index, K.complex i ⟶ (U.push i).obj (L.complex (U.index.obj i))
  compatible : Compatible U K L stage
  limit : C.cocone.pt ⟶ U.limitPush.obj D.cocone.pt
  coprojection : ∀ (i : S.Index) (n : ℤ) (X : S.diagram.obj i),
    ((stage i).f n).hom.app (op X) ≫
      (D.legAt (U.index.obj i) n).hom.app (op ((U.stage i).obj X)) ≫
      (D.cocone.pt.X n).obj.map ((U.projection i).hom.app X).op =
    (C.legAt i n).hom.app (op X) ≫
      (limit.f n).hom.app (op ((S.cocone.ι.app i).toFunctor.obj X))

/-- Compatible lifts of a coefficient change to the two resolution presentations.
Neither the continuity square nor invertibility is assumed. Section maps are
specified on every term; only the ordinary system and extension equations are data.
Source: Stacks 013P, 013S and 08J6
(blueprint: def-per-finite-cover-derived-sections-data). -/
structure Change.Lift {S T : Sites.{u}} {U : SiteChange S T}
    {K : System S} {C : K.Colimit} {L : System T} {D : L.Colimit}
    (h : Change U K C L D) {b c : ℤ} (M : Model K C b) (N : Model L D c) where
  stage : ∀ i : S.Index,
    M.resolved.complex i ⟶ (U.push i).obj (N.resolved.complex (U.index.obj i))
  compatible : Compatible U M.resolved N.resolved stage
  extension : ∀ i : S.Index, M.augmentation.map i ≫ stage i =
    h.stage i ≫ (U.push i).map (N.augmentation.map (U.index.obj i))
  receiver : M.receiver ⟶ U.limitPush.obj N.receiver
  receiverExtension : M.receiverMap ≫ receiver =
    h.limit ≫ U.limitPush.map N.receiverMap
  sections : M.sections.diagram ⟶ U.index ⋙ N.sections.diagram
  stageSections : ∀ i : S.Index,
    IsSectionMap (S.covers i).toGrothendieck (T.covers (U.index.obj i)).toGrothendieck
      (U.stage i) (M.resolved.complex i) (N.resolved.complex (U.index.obj i))
      (stage i) ((M.sections.iso i).inv ≫ sections.app i ≫
        (N.sections.iso (U.index.obj i)).hom)
  limitSections : (S.limitSections).obj M.receiver ⟶ (T.limitSections).obj N.receiver
  receiverSections : IsSectionMap S.limitCovers.toGrothendieck
    T.limitCovers.toGrothendieck U.limit M.receiver N.receiver receiver limitSections

/-- The actual map between the two filtered derived-colimit models.
Source: Stacks 09YP (blueprint: def-per-finite-cover-derived-sections-data). -/
def Change.Lift.sourceMap {S T : Sites.{u}} {U : SiteChange S T}
    {K : System S} {C : K.Colimit} {L : System T} {D : L.Colimit}
    {h : Change U K C L D} {b c : ℤ} {M : Model K C b} {N : Model L D c}
    (v : h.Lift M N) : colimit M.sections.diagram ⟶ colimit N.sections.diagram :=
  colim.map v.sections ≫ colimit.pre N.sections.diagram U.index

/-- The commuting derived continuity square, including a change of sites and index.
Source: Stacks 08J6, 013S, 09YP
(blueprint: def-per-finite-cover-derived-sections-data). -/
def Change.Lift.Commutes {S T : Sites.{u}} {U : SiteChange S T}
    {K : System S} {C : K.Colimit} {L : System T} {D : L.Colimit}
    {h : Change U K C L D} {b c : ℤ} {M : Model K C b} {N : Model L D c}
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] (v : h.Lift M N) : Prop :=
  DerivedCategory.Q.map M.comparison ≫ DerivedCategory.Q.map v.limitSections =
    DerivedCategory.Q.map v.sourceMap ≫ DerivedCategory.Q.map N.comparison

/-- A canonical upper-truncation tower, with actual coefficient and colimit maps.
Inclusions and their factorizations specify the transition maps without choosing
any noncanonical kernel identification.
Source: Stacks, Homology, canonical truncations; Derived Categories 015E
(blueprint: def-per-finite-cover-derived-sections-data). -/
structure Truncations {S : Sites.{u}} (K : System S) (C : K.Colimit) where
  system : ℤ → System S
  colimit : ∀ r : ℤ, (system r).Colimit
  stageIso : ∀ (r : ℤ) (i : S.Index), (system r).complex i ≅ (K.complex i).truncLE r
  limitIso : ∀ r : ℤ, (colimit r).cocone.pt ≅ C.cocone.pt.truncLE r
  inclusion : ∀ r : ℤ, (system r).Map K
  stageInclusion : ∀ (r : ℤ) (i : S.Index),
    (inclusion r).map i = (stageIso r i).hom ≫ (K.complex i).ιTruncLE r
  limitInclusion : ∀ r : ℤ, (colimit r).cocone.pt ⟶ C.cocone.pt
  limitInclusion_eq : ∀ r : ℤ,
    limitInclusion r = (limitIso r).hom ≫ C.cocone.pt.ιTruncLE r
  inclusionCoprojection : ∀ (r : ℤ) (i : S.Index) (n : ℤ),
    (colimit r).legAt i n ≫
      ((S.cocone.ι.app i).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
        (S.covers i).toGrothendieck S.limitCovers.toGrothendieck).map
          ((limitInclusion r).f n) =
    ((inclusion r).map i).f n ≫ C.legAt i n
  transition : ∀ (r s : ℤ), r ≤ s → (system r).Map (system s)
  stageTransition : ∀ (r s : ℤ) (hrs : r ≤ s) (i : S.Index),
    (transition r s hrs).map i ≫ (inclusion s).map i = (inclusion r).map i
  limitTransition : ∀ (r s : ℤ) (_ : r ≤ s),
    (colimit r).cocone.pt ⟶ (colimit s).cocone.pt
  limitTransition_eq : ∀ (r s : ℤ) (hrs : r ≤ s),
    limitTransition r s hrs ≫ limitInclusion s = limitInclusion r
  transitionCoprojection : ∀ (r s : ℤ) (hrs : r ≤ s) (i : S.Index) (n : ℤ),
    (colimit r).legAt i n ≫
      ((S.cocone.ι.app i).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
        (S.covers i).toGrothendieck S.limitCovers.toGrothendieck).map
          ((limitTransition r s hrs).f n) =
    ((transition r s hrs).map i).f n ≫ (colimit s).legAt i n


/-- Lifts of an ordinary coefficient map between two presentations on the same sites.
The limit map is specified by the actual colimit coprojections.
Source: Stacks 013P, 013S, 09YP
(blueprint: def-per-finite-cover-derived-sections-data). -/
structure System.Map.Lift {S : Sites.{u}} {K L : System S} {C : K.Colimit}
    {D : L.Colimit} (h : K.Map L) (g : C.cocone.pt ⟶ D.cocone.pt)
    {b c : ℤ} (M : Model K C b) (N : Model L D c) where
  coprojection : ∀ (i : S.Index) (n : ℤ),
    C.legAt i n ≫
      ((S.cocone.ι.app i).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
        (S.covers i).toGrothendieck S.limitCovers.toGrothendieck).map (g.f n) =
      (h.map i).f n ≫ D.legAt i n
  stage : M.resolved.Map N.resolved
  extension : ∀ i : S.Index, M.augmentation.map i ≫ stage.map i =
    h.map i ≫ N.augmentation.map i
  receiver : M.receiver ⟶ N.receiver
  receiverExtension : M.receiverMap ≫ receiver = g ≫ N.receiverMap
  sections : M.sections.diagram ⟶ N.sections.diagram
  stageSections : ∀ i : S.Index, sections.app i =
    (M.sections.iso i).hom ≫ (S.sections i).map (stage.map i) ≫ (N.sections.iso i).inv

/-- The derived naturality square for an ordinary coefficient map.
Source: Stacks 013S, 09YP (blueprint: def-per-finite-cover-derived-sections-data). -/
def System.Map.Lift.Commutes {S : Sites.{u}} {K L : System S} {C : K.Colimit}
    {D : L.Colimit} {h : K.Map L} {g : C.cocone.pt ⟶ D.cocone.pt}
    {b c : ℤ} {M : Model K C b} {N : Model L D c}
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] (v : h.Lift g M N) : Prop :=
  DerivedCategory.Q.map M.comparison ≫
      DerivedCategory.Q.map ((S.limitSections).map v.receiver) =
    DerivedCategory.Q.map (colim.map v.sections) ≫ DerivedCategory.Q.map N.comparison

/-- A refinement of resolution choices for the very same coefficient system.
Source: Stacks 013P, 013S (blueprint: def-per-finite-cover-derived-sections-data). -/
structure Model.Refinement {S : Sites.{u}} {K : System S} {C : K.Colimit}
    {b c : ℤ} (M : Model K C b) (N : Model K C c) where
  stage : M.resolved.Map N.resolved
  extension : ∀ i : S.Index, M.augmentation.map i ≫ stage.map i = N.augmentation.map i
  receiver : M.receiver ⟶ N.receiver
  receiverExtension : M.receiverMap ≫ receiver = N.receiverMap
  sections : M.sections.diagram ⟶ N.sections.diagram
  stageSections : ∀ i : S.Index, sections.app i =
    (M.sections.iso i).hom ≫ (S.sections i).map (stage.map i) ≫ (N.sections.iso i).inv

/-- The comparison square for two choices of compatible resolutions.
Source: Stacks 013S (blueprint: def-per-finite-cover-derived-sections-data). -/
def Model.Refinement.Commutes {S : Sites.{u}} {K : System S} {C : K.Colimit}
    {b c : ℤ} {M : Model K C b} {N : Model K C c}
    [HasDerivedCategory.{w} AddCommGrpCat.{u}] (v : M.Refinement N) : Prop :=
  DerivedCategory.Q.map M.comparison ≫
      DerivedCategory.Q.map ((S.limitSections).map v.receiver) =
    DerivedCategory.Q.map (colim.map v.sections) ≫ DerivedCategory.Q.map N.comparison

/-- Resolution models and lifts for all canonical upper truncations and all their
inclusions. The same lower bound is retained even when r is below it.
Source: Stacks, canonical truncations and Derived Categories 015E
(blueprint: def-per-finite-cover-derived-sections-data). -/
structure Truncations.Models {S : Sites.{u}} {K : System S} {C : K.Colimit}
    (V : Truncations K C) (b : ℤ) where
  original : Model K C b
  truncation : ∀ r : ℤ, Model (V.system r) (V.colimit r) b
  inclusion : ∀ r : ℤ,
    (V.inclusion r).Lift (V.limitInclusion r) (truncation r) original
  transition : ∀ (r s : ℤ) (hrs : r ≤ s),
    (V.transition r s hrs).Lift (V.limitTransition r s hrs) (truncation r) (truncation s)

end CategoryTheory.FiniteCoverDerivedSections
