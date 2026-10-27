/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap

public import Sheaf.CategoryTheory.TotalSiteSheafSystems
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.ContinuousCocontinuousRingedRestriction
import Sheaf.CategoryTheory.NativeRingedRestrictionSheafification
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

/-! # Ringed total category of a semisimplicial diagram

Source: Stacks Project, spaces-simplicial.tex, Tags 09WC, 09WF, 0D72 and 0D70;
sites-cohomology.tex, Tags 06YY and 0D6D, with the face-only index
(blueprint: lem-sfb-semisimplicial-ringed-total-category).

The input ring presheaf on the Grothendieck category is the coherent ring system:
its restrictions along Cartesian lifts are the adjoints of the structural ring maps.
The fibre sheaf condition is the only sheaf condition assumed on this input.
Module systems are actual module presheaves on this category with fibre sheaf
conditions; functoriality is precisely the semilinear identity and composition law.
The output retains the canonical maps, including their representative normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory
open SheafOfModules

namespace CategoryTheory.SemisimplicialRingedTotal

/-- A small commutative ringed site. Source: Stacks 0D72
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure Site where
  C : Type u
  [category : SmallCategory C]
  J : GrothendieckTopology C
  ring : Sheaf J CommRingCat.{u}

attribute [instance] Site.category

/-- The existing ring sheaf with commutativity forgotten. Source: Stacks 0D72
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
abbrev Site.rings (X : Site.{u}) :=
  (sheafCompose X.J (forget₂ CommRingCat RingCat)).obj X.ring

/-- The dependency's actual category of module sheaves. Source: Stacks 0D72
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
abbrev Site.modules (X : Site.{u}) := ringedSiteModules.{u} X.rings

/-- A fixed standard localization in the larger size universe. Source: Stacks 05RU
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
instance Site.hasDerived (X : Site.{u}) : HasDerivedCategory.{u + 1} X.modules :=
  HasDerivedCategory.standard X.modules

/-- Ordinary unbounded derived category, without a boundedness restriction. Source: Stacks 05RU
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
abbrev Site.D (X : Site.{u}) := DerivedCategory.{u + 1} X.modules

/-- Underlying sheaves of sets of modules. Source: Stacks 03D7
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
abbrev Site.sets (X : Site.{u}) :=
  SheafOfModules.toSheaf X.rings ⋙ sheafCompose X.J (forget AddCommGrpCat.{u})

/-- Flat-term K-flat representatives. Source: Stacks 06YS, 0G7E
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def Site.flat (X : Site.{u}) (P : CochainComplex X.modules ℤ) : Prop :=
  P.IsKFlatIndependentCoefficients ∧ ∀ q : ℤ, IsFlatOnSite (J := X.J) (R := X.ring) (P.X q)

/-- The canonical ordinary and derived module pullback for a given ringed morphism.
The scalar-extension object/map formulas and the underlying adjunction formula
exclude arbitrary adjunctions or arbitrary comparison maps. Source: Stacks 03D7, 06YY
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure Pullback {X Y : Site.{u}} (f : RingedToposMorphism X.rings Y.rings) where
  inverseRing : Sheaf X.J CommRingCat.{u}
  algebraic : AlgebraicInverseImage f.inverse Y.ring inverseRing
  ringMap : inverseRing ⟶ X.ring
  structural : algebraic.ringUnderlying.hom ≫
      (sheafCompose X.J (forget CommRingCat.{u})).map ringMap = f.ringMap
  ordinary : Y.modules ⥤ X.modules
  object_eq : ∀ M : Y.modules,
    ordinary.obj M = changeOfRings ringMap (algebraic.modules.obj M)
  map_eq : ∀ {M N : Y.modules} (b : M ⟶ N),
    ordinary.map b = eqToHom (object_eq M) ≫
      changeOfRingsHom ringMap (algebraic.modules.obj M) (algebraic.modules.map b) ≫
        eqToHom (object_eq N).symm
  [additive : ordinary.Additive]
  adjunction : ordinary ⊣ f.modules
  insertion : ∀ M : Y.modules, f.inverse.obj (Y.sets.obj M) ⟶ X.sets.obj (ordinary.obj M)
  insertion_one : ∀ (M : Y.modules) (U : X.Cᵒᵖ) (m : (algebraic.modules.obj M).val.obj U),
    (algebraic.moduleUnderlying.hom.app M ≫ insertion M).hom.app U m =
      (eqToHom (object_eq M).symm).val.app U
        (ringedComparisonScalarSection ringMap (algebraic.modules.obj M) U 1 m)
  adjunction_underlying : ∀ (M : Y.modules) (N : X.modules) (b : ordinary.obj M ⟶ N),
    Y.sets.map (adjunction.homEquiv M N b) ≫ f.underlying.hom.app N =
      f.adj.homEquiv (Y.sets.obj M) (X.sets.obj N) (insertion M ≫ X.sets.map b)
  derived : Y.D ⥤ X.D
  epsilon : DerivedCategory.Qh ⋙ derived ⟶
    ordinary.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  isLeftDerived : derived.IsLeftDerivedFunctor epsilon
    (HomotopyCategory.quasiIso Y.modules (ComplexShape.up ℤ))
  flat_computation : ∀ P : CochainComplex Y.modules ℤ, Y.flat P →
    IsIso (derivedPullbackComplexComparison ordinary derived epsilon P)
  preserves_flat : ∀ P : CochainComplex Y.modules ℤ, Y.flat P →
    X.flat ((ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

attribute [instance] Pullback.additive

/-- The recorded comparison, on a complex, for an actual left derived functor.
Source: Stacks 06YY (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
abbrev Pullback.alpha {X Y : Site.{u}} {f : RingedToposMorphism X.rings Y.rings}
    (p : Pullback f) (P : CochainComplex Y.modules ℤ) :=
  derivedPullbackComplexComparison p.ordinary p.derived p.epsilon P

/-- Composition comparisons fixed by insertion on modules and by K-flat representatives
on derived categories. Source: Stacks 0D6D, 03EL
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure Composition {X Y Z : Site.{u}}
    {f : RingedToposMorphism X.rings Y.rings}
    {g : RingedToposMorphism Y.rings Z.rings}
    {h : RingedToposMorphism X.rings Z.rings}
    (p : Pullback f) (q : Pullback g) (r : Pullback h)
    (θ : h.inverse ≅ g.inverse ⋙ f.inverse) where
  ordinary : r.ordinary ≅ q.ordinary ⋙ p.ordinary
  insertion : ∀ M : Z.modules,
    r.insertion M ≫ X.sets.map (ordinary.hom.app M) =
      θ.hom.app (Z.sets.obj M) ≫ f.inverse.map (q.insertion M) ≫
        p.insertion (q.ordinary.obj M)
  derived : r.derived ≅ q.derived ⋙ p.derived
  representative : ∀ P : CochainComplex Z.modules ℤ, Z.flat P →
    derived.hom.app (DerivedCategory.Q.obj P) ≫ p.derived.map (q.alpha P) ≫
        p.alpha ((q.ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      r.alpha P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary.hom (ComplexShape.up ℤ)).app P)

variable {F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u}}

/-- Coherent input ring system, written as its actual total presheaf. The presheaf
functor laws are the unit/composition laws of the adjoint structural maps.
Source: Stacks 09WF, 0D72 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure RingDiagram (D : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F) where
  presheaf : (Pseudofunctor.CoGrothendieck F)ᵒᵖ ⥤ CommRingCat.{u}
  fibre_sheaf : ∀ i : SemiSimplexCategoryᵒᵖ,
    Presheaf.IsSheaf (D.coverage i).toGrothendieck
      ((Pseudofunctor.CoGrothendieck.ι F i).op ⋙ presheaf)

variable {D : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F} (R : RingDiagram D)

/-- The given fibre ringed site. Source: Stacks 09WF, 0D72
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def RingDiagram.fibre (i : SemiSimplexCategoryᵒᵖ) : Site.{u} where
  C := F.obj ⟨op i⟩
  J := (D.coverage i).toGrothendieck
  ring := ⟨_, R.fibre_sheaf i⟩

/-- A semilinear system is a module presheaf on the total category whose restrictions
are module sheaves. All transition, identity, composition and semilinearity laws are
those of `PresheafOfModules`, including at nonvertical arrows. Source: Stacks 09WF, 0D72
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def RingDiagram.systemProperty : ObjectProperty
    (PresheafOfModules.{u} (R.presheaf ⋙ forget₂ CommRingCat RingCat)) :=
  fun M => ∀ i : SemiSimplexCategoryᵒᵖ,
    Presheaf.IsSheaf (D.coverage i).toGrothendieck
      (((PresheafOfModules.pushforward₀ (Pseudofunctor.CoGrothendieck.ι F i) _).obj M).presheaf)

/-- The actual category of component module systems with compatible morphisms.
Source: Stacks 09WF, 0D72 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
abbrev RingDiagram.Systems := R.systemProperty.FullSubcategory

/-- Component evaluation for the explicit system category. Source: Stacks 0D72
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def RingDiagram.systemEvaluation (i : SemiSimplexCategoryᵒᵖ) :
    R.Systems ⥤ (R.fibre i).modules where
  obj M := ⟨(PresheafOfModules.pushforward₀
    (Pseudofunctor.CoGrothendieck.ι F i) _).obj M.obj, M.property i⟩
  map b := ⟨(PresheafOfModules.pushforward₀
    (Pseudofunctor.CoGrothendieck.ι F i) _).map b.hom⟩

/-- Coherent augmentation of the given ringed diagram to an arbitrary ringed topos.
The comparisons have the specified identity and composition, and preserve the ring map.
Source: Stacks 0D70 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure Augmentation (S : Site.{u})
    (face : ∀ {i j : SemiSimplexCategoryᵒᵖ}, (i ⟶ j) →
      RingedToposMorphism (R.fibre i).rings (R.fibre j).rings)
    (faceId : ∀ i, (face (𝟙 i)).inverse ≅ 𝟭 _)
    (faceComp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k),
      (face (a ≫ b)).inverse ≅ (face b).inverse ⋙ (face a).inverse) where
  map : ∀ i, RingedToposMorphism (R.fibre i).rings S.rings
  comparison : ∀ {i j} (a : i ⟶ j),
    (map i).inverse ≅ (map j).inverse ⋙ (face a).inverse
  ring : ∀ {i j} (a : i ⟶ j),
    (map i).ringMap = (comparison a).hom.app
      ((sheafCompose S.J (forget RingCat.{u})).obj S.rings) ≫
        (face a).inverse.map (map j).ringMap ≫ (face a).ringMap
  identity : ∀ (i : SemiSimplexCategoryᵒᵖ) (T : Sheaf S.J (Type u)),
    (comparison (𝟙 i)).hom.app T ≫ (faceId i).hom.app ((map i).inverse.obj T) = 𝟙 _
  composition : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k) (T : Sheaf S.J (Type u)),
    (comparison (a ≫ b)).hom.app T ≫ (faceComp a b).hom.app ((map k).inverse.obj T) =
      (comparison a).hom.app T ≫ (face a).inverse.map ((comparison b).hom.app T)


/-- The total ringed site, once the asserted total sheaf condition is supplied.
Source: Stacks 09WF, 0D72 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def RingDiagram.total (h : Presheaf.IsSheaf D.totalTopology R.presheaf) : Site.{u} where
  C := Pseudofunctor.CoGrothendieck F
  J := D.totalTopology
  ring := ⟨R.presheaf, h⟩

/-- Exact component evaluation, with its actual termwise derived functor.
Source: Stacks 0D72, 015F (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure Evaluation (X Y : Site.{u}) where
  ordinary : X.modules ⥤ Y.modules
  [additive : ordinary.Additive]
  [limits : PreservesFiniteLimits ordinary]
  [colimits : PreservesFiniteColimits ordinary]

attribute [instance] Evaluation.additive Evaluation.limits Evaluation.colimits

/-- Termwise evaluation in the ordinary unbounded derived category.
Source: Stacks 015F (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
abbrev Evaluation.derived {X Y : Site.{u}} (e : Evaluation X Y) :=
  e.ordinary.mapDerivedCategory

/-- Identity comparison fixed by scalar insertion and by flat K-flat complexes.
Source: Stacks 03EL, 0D6D (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure Identity {X : Site.{u}} {f : RingedToposMorphism X.rings X.rings}
    (p : Pullback f) (θ : f.inverse ≅ 𝟭 _) where
  ordinary : p.ordinary ≅ 𝟭 X.modules
  insertion : ∀ M : X.modules,
    p.insertion M ≫ X.sets.map (ordinary.hom.app M) = θ.hom.app (X.sets.obj M)
  derived : p.derived ≅ 𝟭 X.D
  representative : ∀ P : CochainComplex X.modules ℤ, X.flat P →
    derived.hom.app (DerivedCategory.Q.obj P) = p.alpha P ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary.hom (ComplexShape.up ℤ)).app P)

/-- Simultaneous module equivalence, exact evaluations, and canonical derived transitions.
All comparisons are fixed on the given presheaf, scalar insertions and K-flat models.
Source: Stacks 09WF, 0D72, 06YY, 0D6D
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure Presentation (h : Presheaf.IsSheaf D.totalTopology R.presheaf) where
  equivalence : (R.total h).modules ≌ R.Systems
  forget_eq : equivalence.functor ⋙ R.systemProperty.ι =
    SheafOfModules.forget (R.total h).rings
  evaluation : ∀ i : SemiSimplexCategoryᵒᵖ, Evaluation (R.total h) (R.fibre i)
  evaluation_eq : ∀ i,
    (evaluation i).ordinary = equivalence.functor ⋙ R.systemEvaluation i
  conservative : ∀ {M N : (R.total h).modules} (b : M ⟶ N),
    (∀ i : SemiSimplexCategoryᵒᵖ, IsIso ((evaluation i).ordinary.map b)) → IsIso b
  face : ∀ {i j : SemiSimplexCategoryᵒᵖ}, (i ⟶ j) →
    RingedToposMorphism (R.fibre i).rings (R.fibre j).rings
  face_inverse : ∀ {i j} (a : i ⟶ j), (face a).inverse = D.inverseImage a
  face_direct : ∀ {i j} (a : i ⟶ j), (face a).direct = D.directImage a
  face_adjunction : ∀ {i j} (a : i ⟶ j), HEq (face a).adj (D.imageAdjunction a)
  face_ring : ∀ {i j} (a : i ⟶ j) (V : F.obj ⟨op j⟩),
    HEq (((face a).adj.homEquiv _ _ (face a).ringMap).hom.app (op V))
      ((forget CommRingCat.{u}).map
        (R.presheaf.map (Pseudofunctor.CoGrothendieck.cartesianLift V a).op))
  faceId : ∀ i, (face (𝟙 i)).inverse ≅ 𝟭 _
  faceId_eq : ∀ i, HEq (faceId i) (D.inverseImageId i)
  faceComp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k),
    (face (a ≫ b)).inverse ≅ (face b).inverse ⋙ (face a).inverse
  faceComp_eq : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k),
    HEq (faceComp a b) (D.inverseImageComp a b).symm
  pullback : ∀ {i j} (a : i ⟶ j), Pullback (face a)
  identity : ∀ i, Identity (pullback (𝟙 i)) (faceId i)
  composition : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k),
    Composition (pullback a) (pullback b) (pullback (a ≫ b)) (faceComp a b)
  transition : ∀ {i j} (a : i ⟶ j),
    (evaluation j).ordinary ⋙ (pullback a).ordinary ⟶ (evaluation i).ordinary
  transition_restriction : ∀ (M : (R.total h).modules) {i j} (a : i ⟶ j)
      (V : F.obj ⟨op j⟩),
    HEq (((R.fibre j).sets.map
      ((pullback a).adjunction.homEquiv _ _ ((transition a).app M)) ≫
        (face a).underlying.hom.app ((evaluation i).ordinary.obj M)).hom.app (op V))
      ((forget AddCommGrpCat.{u}).map
        (M.val.presheaf.map (Pseudofunctor.CoGrothendieck.cartesianLift V a).op))
  transition_id : ∀ i (M : (R.total h).modules),
    (transition (𝟙 i)).app M = (identity i).ordinary.hom.app ((evaluation i).ordinary.obj M)
  transition_comp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k) (M : (R.total h).modules),
    (composition a b).ordinary.hom.app ((evaluation k).ordinary.obj M) ≫
      (pullback a).ordinary.map ((transition b).app M) ≫ (transition a).app M =
        (transition (a ≫ b)).app M
  derivedTransition : ∀ {i j} (a : i ⟶ j),
    (evaluation j).derived ⋙ (pullback a).derived ⟶ (evaluation i).derived
  derived_representative : ∀ (P : CochainComplex (R.total h).modules ℤ),
    (R.total h).flat P → ∀ {i j} (a : i ⟶ j),
      ∃ t : ((pullback a).ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((evaluation j).ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
        ((evaluation i).ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
      (∀ q : ℤ, t.f q = (transition a).app (P.X q)) ∧
      (derivedTransition a).app (DerivedCategory.Q.obj P) ≫
          (evaluation i).ordinary.mapDerivedCategoryFactors.hom.app P =
        (pullback a).derived.map
            ((evaluation j).ordinary.mapDerivedCategoryFactors.hom.app P) ≫
          (pullback a).alpha
            (((evaluation j).ordinary.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map t
  derived_id : ∀ i (B : (R.total h).D),
    (derivedTransition (𝟙 i)).app B =
      (identity i).derived.hom.app ((evaluation i).derived.obj B)
  derived_comp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k) (B : (R.total h).D),
    (composition a b).derived.hom.app ((evaluation k).derived.obj B) ≫
      (pullback a).derived.map ((derivedTransition b).app B) ≫ (derivedTransition a).app B =
        (derivedTransition (a ≫ b)).app B
  fibreMap : ∀ i, RingedToposMorphism (R.fibre i).rings (R.total h).rings
  fibre_inverse : ∀ i (T : Sheaf D.totalTopology (Type u)),
    ((fibreMap i).inverse.obj T).obj = (Pseudofunctor.CoGrothendieck.ι F i).op ⋙ T.obj
  fibre_inverse_map : ∀ i {T U : Sheaf D.totalTopology (Type u)} (b : T ⟶ U),
    HEq ((fibreMap i).inverse.map b).hom
      (Functor.whiskerLeft (Pseudofunctor.CoGrothendieck.ι F i).op b.hom)
  fibre_ring : ∀ i (U : (R.fibre i).Cᵒᵖ)
    (x : ((fibreMap i).inverse.obj
      ((sheafCompose D.totalTopology (forget RingCat.{u})).obj (R.total h).rings)).obj.obj U),
    HEq ((fibreMap i).ringMap.hom.app U x) x
  setsTransition : ∀ {i j} (a : i ⟶ j),
    (fibreMap j).inverse ⋙ (face a).inverse ⟶ (fibreMap i).inverse
  setsTransition_restriction : ∀ (T : Sheaf D.totalTopology (Type u))
      {i j} (a : i ⟶ j) (V : F.obj ⟨op j⟩),
    HEq (((face a).adj.homEquiv _ _ ((setsTransition a).app T)).hom.app (op V))
      (T.obj.map (Pseudofunctor.CoGrothendieck.cartesianLift V a).op)
  fibrePullback : ∀ i, Pullback (fibreMap i)
  fibreEvaluation : ∀ i, (fibrePullback i).ordinary ≅ (evaluation i).ordinary
  fibreEvaluation_insertion : ∀ i (M : (R.total h).modules) (U : (R.fibre i).Cᵒᵖ)
    (x : ((fibreMap i).inverse.obj ((R.total h).sets.obj M)).obj.obj U),
    HEq (((fibrePullback i).insertion M ≫
      (R.fibre i).sets.map ((fibreEvaluation i).hom.app M)).hom.app U x) x
  fibreDerived : ∀ i, (fibrePullback i).derived ≅ (evaluation i).derived
  fibreDerived_model : ∀ i (P : CochainComplex (R.total h).modules ℤ),
    (R.total h).flat P →
    (fibreDerived i).hom.app (DerivedCategory.Q.obj P) ≫
      (evaluation i).ordinary.mapDerivedCategoryFactors.hom.app P =
      (fibrePullback i).alpha P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (fibreEvaluation i).hom (ComplexShape.up ℤ)).app P)
  cohomology_criterion :
    (∀ {i j} (a : i ⟶ j), PreservesFiniteLimits (pullback a).ordinary ∧
      PreservesFiniteColimits (pullback a).ordinary) →
    ∀ B : (R.total h).D,
      (∀ {i j} (a : i ⟶ j), IsIso ((derivedTransition a).app B)) ↔
      ∀ (q : ℤ) {i j} (a : i ⟶ j),
        IsIso ((transition a).app ((DerivedCategory.homologyFunctor (R.total h).modules q).obj B))


/-- Cartesian means precisely that all the constructed derived transitions are invertible.
Source: Stacks 09WC, 06YY, face-only adaptation
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def Presentation.IsCartesian {R : RingDiagram D}
    {h : Presheaf.IsSheaf D.totalTopology R.presheaf} (P : Presentation R h)
    (B : (R.total h).D) : Prop :=
  ∀ {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j), IsIso ((P.derivedTransition a).app B)

/-- The total augmentation and its canonical ordinary and derived component comparisons.
The last two equations identify its transitions with the canonical composition
comparisons, without assuming exactness of any face or augmentation pullback.
Source: Stacks 0D70, 0D72, 06YY, 0D6D
(blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure AugmentationPresentation {R : RingDiagram D}
    {h : Presheaf.IsSheaf D.totalTopology R.presheaf} (P : Presentation R h)
    (S : Site.{u}) (A : Augmentation R S P.face P.faceId P.faceComp) where
  map : RingedToposMorphism (R.total h).rings S.rings
  pullback : Pullback map
  components : ∀ i, Pullback (A.map i)
  sets : ∀ i, (A.map i).inverse ≅ map.inverse ⋙ (P.fibreMap i).inverse
  sets_ring : ∀ i,
    (A.map i).ringMap = (sets i).hom.app
      ((sheafCompose S.J (forget RingCat.{u})).obj S.rings) ≫
        (P.fibreMap i).inverse.map map.ringMap ≫ (P.fibreMap i).ringMap
  sets_transition : ∀ {i j} (a : i ⟶ j) (T : Sheaf S.J (Type u)),
    (A.comparison a).hom.app T ≫ (P.face a).inverse.map ((sets j).hom.app T) ≫
      (P.setsTransition a).app (map.inverse.obj T) = (sets i).hom.app T
  composition : ∀ i,
    Composition (P.fibrePullback i) pullback (components i) (sets i)
  component : ∀ i, pullback.ordinary ⋙ (P.evaluation i).ordinary ≅ (components i).ordinary
  component_canonical : ∀ i, component i =
    Functor.isoWhiskerLeft pullback.ordinary (P.fibreEvaluation i).symm ≪≫
      (composition i).ordinary.symm
  derivedComponent : ∀ i,
    pullback.derived ⋙ (P.evaluation i).derived ≅ (components i).derived
  derivedComponent_canonical : ∀ i (E : S.D),
    (derivedComponent i).inv.app E =
      (composition i).derived.hom.app E ≫
        (P.fibreDerived i).hom.app (pullback.derived.obj E)
  faceComposition : ∀ {i j} (a : i ⟶ j),
    Composition (P.pullback a) (components j) (components i) (A.comparison a)
  component_transition : ∀ {i j} (a : i ⟶ j) (E : S.modules),
    (P.transition a).app (pullback.ordinary.obj E) ≫ (component i).hom.app E =
      (P.pullback a).ordinary.map ((component j).hom.app E) ≫
        (faceComposition a).ordinary.inv.app E
  derivedComponent_transition : ∀ {i j} (a : i ⟶ j) (E : S.D),
    (P.derivedTransition a).app (pullback.derived.obj E) ≫ (derivedComponent i).hom.app E =
      (P.pullback a).derived.map ((derivedComponent j).hom.app E) ≫
        (faceComposition a).derived.inv.app E

/-- The ringed total category, its exact conservative evaluations, its derived
cartesian criterion, and arbitrary coherent augmentation comparisons.

Source: Stacks Project, spaces-simplicial.tex, Tags 09WC
(lemma-simplicial-site-site), 09WF (lemma-describe-sheaves-simplicial-site-site),
0D72 (lemma-restriction-module-to-components-site), 0D70 (lemma-augmentation-site),
with the injective-order-map index; sites-cohomology.tex, Tags 06YS, 06YY, 0G7E, 0D6D
(blueprint: lem-sfb-semisimplicial-ringed-total-category).

Proof: (1) Apply totalSite_of_coherent_pseudofunctor and totalSite_sheaf_systems
with I = SemiSimplexCategory opposite. The finite-product-compatible systems
equivalence assembles the ring operations. The module action equations say exactly
that restrictions are semilinear; scalar extension identifies these with linear
maps from the indicated module pullbacks. Compatible component maps give exactly
the morphisms, hence the displayed equivalence, fixed over module presheaves.
(2) Each fibre inclusion is continuous and cocontinuous: covering pullbacks are
computed in the fibre and all generating covers are vertical. Construct its ringed
restriction by continuous_cocontinuous_ringed_restriction; its module inverse image
O_n tensor M|_n is identified with evaluation by r tensor m mapped to r m. Kernels are sectionwise;
cokernels are sheafified sectionwise cokernels, and sheafificationRestriction
commutes with this restriction. Thus evaluation preserves finite limits and
colimits. Component inverses commute with transitions, proving conservativity.
(3) mapDerivedCategory and mapDerivedCategoryFactors give termwise evaluation,
which exactFunctor_derivedFunctor identifies with both derived functors.
(4) Choose a flat-term K-flat resolution of a total complex. Evaluation is the
module inverse image of the fibre morphism and preserves this class, as does every
ringed pullback. Localize the actual transition chain maps. The representative
comparisons of ringedTopoiDerivedPullbackIndependent prove naturality and resolution
independence. The ordinary insertions fix composition by tensor reassociation;
ringedDerivedMonoidalComparisons identifies the resulting derived comparison on
these representatives with the canonical composition comparison. The chain-level
cocycle proves the derived cocycle and the unit law. No assertion that all derived
systems lift to total complexes is used.
(5) When the face pullbacks are exact, their derived functors are computed on every
complex. Exact-functor cohomology compatibility identifies cohomology of the derived
transition with the transition of each cohomology system. A chain map is a
quasi-isomorphism exactly when all its integer cohomology maps are invertible,
proving the stated equivalence.
(6) A coherent augmentation gives inverse image by its component inverse images.
Its right adjoint is the all-arrow equalizer of the products of component direct
images; the systems equivalence proves the adjunction. The structural ring maps
assemble to give the total ringed morphism.
(7) Restriction commutes with sectionwise scalar extension and its sheafification.
Consequently total module pullback has the component pullbacks. The transition is
tensor reassociation, r tensor (s tensor x) mapped to r c(s) tensor x, whose inverse
inserts 1. The prescribed insertion equations express precisely this comparison.
(8) Resolve the augmented input by one flat-term K-flat complex. The same complex
computes all component pullbacks. Their ordinary comparison computes the canonical
derived comparison by the cited composition theorem. Naturality and resolution
independence descend its unit and composition equations. This gives every
augmentation clause without exactness assumptions on face or augmentation pullbacks. -/
theorem semisimplicial_ringed_total_category
    {F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u}}
    (D : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F)
    (geometric : ∀ (i j : SemiSimplexCategoryᵒᵖ) (a : i ⟶ j),
      PreservesFiniteLimits (D.inverseImage a))
    (R : RingDiagram D) :
    ∃ (h : Presheaf.IsSheaf D.totalTopology R.presheaf) (P : Presentation R h),
      ∀ (S : Site.{u}) (A : Augmentation R S P.face P.faceId P.faceComp),
        Nonempty (AugmentationPresentation P S A) := by
  sorry

end CategoryTheory.SemisimplicialRingedTotal

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The restricted face diagram, including its actual augmentation arrows.
Source: Stacks 09WF (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
abbrev spaceFaceDiagram (U : SimplicialObject (Over X)) :=
  SemiSimplexCategory.toSimplexCategory.op ⋙ U

/-- Tensor identity on the actual face structure map.
Source: Stacks 0D72 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def spaceFaceIdentity (U : SimplicialObject (Over X)) (n : SemiSimplexCategory) :
    moduleTensorPullback ((spaceFaceDiagram U).map (𝟙 n).op).left ≅
      𝟭 (((spaceFaceDiagram U).obj (op n)).left.Modules) :=
  eqToIso (congrArg moduleTensorPullback
    (congrArg Over.Hom.left ((spaceFaceDiagram U).map_id (op n)))) ≪≫
      moduleTensorPullbackId _

/-- Tensor composition is the normalized associativity isomorphism, never an arbitrary iso.
Source: Stacks 0D72 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def spaceFaceComposition (U : SimplicialObject (Over X))
    {l m n : SemiSimplexCategory} (a : l ⟶ m) (b : m ⟶ n) :
    moduleTensorPullback ((spaceFaceDiagram U).map (a ≫ b).op).left ≅
      moduleTensorPullback ((spaceFaceDiagram U).map a.op).left ⋙
        moduleTensorPullback ((spaceFaceDiagram U).map b.op).left :=
  eqToIso (congrArg moduleTensorPullback
    (congrArg Over.Hom.left ((spaceFaceDiagram U).map_comp b.op a.op))) ≪≫
      (moduleTensorComposition ((spaceFaceDiagram U).map b.op).left
        ((spaceFaceDiagram U).map a.op).left).symm

/-- The augmentation's canonical tensor-composition comparison.
Source: Stacks 0D70 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def spaceFaceAugmentation (U : SimplicialObject (Over X))
    {m n : SemiSimplexCategory} (a : m ⟶ n) :
    moduleTensorPullback ((spaceFaceDiagram U).obj (op n)).hom ≅
      moduleTensorPullback ((spaceFaceDiagram U).obj (op m)).hom ⋙
        moduleTensorPullback ((spaceFaceDiagram U).map a.op).left :=
  (eqToIso (congrArg moduleTensorPullback
    (Over.w ((spaceFaceDiagram U).map a.op)))).symm ≪≫
      (moduleTensorComposition ((spaceFaceDiagram U).map a.op).left
        ((spaceFaceDiagram U).obj (op m)).hom).symm

/-- Ordinary module systems, before imposing either cartesianness or quasi-coherence.
Source: Stacks 09WF, 0D72 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure SpaceFaceModuleSystem (U : SimplicialObject (Over X)) where
  obj (n : SemiSimplexCategory) : ((spaceFaceDiagram U).obj (op n)).left.Modules
  transition {m n : SemiSimplexCategory} (a : m ⟶ n) :
    (moduleTensorPullback ((spaceFaceDiagram U).map a.op).left).obj (obj m) ⟶ obj n
  identity (n : SemiSimplexCategory) :
    transition (𝟙 n) = (spaceFaceIdentity U n).hom.app (obj n)
  composition {l m n : SemiSimplexCategory} (a : l ⟶ m) (b : m ⟶ n) :
    transition (a ≫ b) = (spaceFaceComposition U a b).hom.app (obj l) ≫
      (moduleTensorPullback ((spaceFaceDiagram U).map b.op).left).map (transition a) ≫
        transition b

/-- Component maps commuting with every face transition.
Source: Stacks 09WF (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
@[ext] structure SpaceFaceModuleHom {U : SimplicialObject (Over X)}
    (M N : SpaceFaceModuleSystem U) where
  app (n : SemiSimplexCategory) : M.obj n ⟶ N.obj n
  naturality {m n : SemiSimplexCategory} (a : m ⟶ n) :
    (moduleTensorPullback ((spaceFaceDiagram U).map a.op).left).map (app m) ≫
      N.transition a = M.transition a ≫ app n

/-- The ordinary category of systems and compatible component maps.
Source: Stacks 09WF (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
instance spaceFaceModuleCategory (U : SimplicialObject (Over X)) :
    Category (SpaceFaceModuleSystem U) where
  Hom := SpaceFaceModuleHom
  id M := ⟨fun n ↦ 𝟙 (M.obj n), by simp⟩
  comp a b := ⟨fun n ↦ a.app n ≫ b.app n, by
    intro m n f
    rw [Functor.map_comp, Category.assoc, b.naturality, ← Category.assoc,
      a.naturality, Category.assoc]⟩
  id_comp a := by ext n; simp
  comp_id a := by ext n; simp
  assoc a b c := by ext n; simp [Category.assoc]

/-- Ordinary component evaluation.
Source: Stacks 0D72 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def spaceFaceEvaluation (U : SimplicialObject (Over X)) (n : SemiSimplexCategory) :
    SpaceFaceModuleSystem U ⥤ ((spaceFaceDiagram U).obj (op n)).left.Modules where
  obj M := M.obj n
  map f := f.app n

/-- The two injections selecting the vertices of an edge.
Source: Stacks 0D70 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def spaceFaceVertex (i : Fin 2) : SemiSimplexCategory.mk 0 ⟶ SemiSimplexCategory.mk 1 :=
  SemiSimplexCategory.homOfMono (SimplexCategory.δ i)

/-- The two ordinary module arrows defining augmentation direct image. Each is the
adjoint of tensor composition followed by the degree-zero counit and the edge transition.
Source: Stacks 0D70 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
def spaceFaceEqualizerArrow {U : SimplicialObject (Over X)}
    (M : SpaceFaceModuleSystem U) (i : Fin 2) :
    (moduleDirectImage ((spaceFaceDiagram U).obj (op (.mk 0))).hom).obj (M.obj (.mk 0)) ⟶
      (moduleDirectImage ((spaceFaceDiagram U).obj (op (.mk 1))).hom).obj (M.obj (.mk 1)) :=
  (moduleTensorAdjunction ((spaceFaceDiagram U).obj (op (.mk 1))).hom).homEquiv _ _
    ((spaceFaceAugmentation U (spaceFaceVertex i)).hom.app _ ≫
      (moduleTensorPullback ((spaceFaceDiagram U).map (spaceFaceVertex i).op).left).map
        ((moduleTensorAdjunction ((spaceFaceDiagram U).obj (op (.mk 0))).hom).counit.app
          (M.obj (.mk 0))) ≫ M.transition (spaceFaceVertex i))

/-- The ordinary tensor augmentation and its ordinary direct image. The component
comparison fixes the tensor pullback and all its face transitions. The direct-image
object is the actual equalizer, and the hom-equivalence is normalized by its degree-zero
inclusion and the existing module adjunction. Thus its adjunction cannot be freely twisted.
This is the small-coefficient systems presentation of the enlarged ringed total category.
Source: Stacks 0D70, 0D72 (blueprint: lem-sfb-semisimplicial-ringed-total-category). -/
structure SpaceFaceAugmentationModel (U : SimplicialObject (Over X)) where
  pullback : X.Modules ⥤ SpaceFaceModuleSystem U
  component (n : SemiSimplexCategory) :
    pullback ⋙ spaceFaceEvaluation U n ≅
      moduleTensorPullback ((spaceFaceDiagram U).obj (op n)).hom
  transition {m n : SemiSimplexCategory} (a : m ⟶ n) (N : X.Modules) :
    (pullback.obj N).transition a ≫ (component n).hom.app N =
      (moduleTensorPullback ((spaceFaceDiagram U).map a.op).left).map
        ((component m).hom.app N) ≫ (spaceFaceAugmentation U a).inv.app N
  direct : SpaceFaceModuleSystem U ⥤ X.Modules
  directObject (M : SpaceFaceModuleSystem U) :
    direct.obj M = equalizer (spaceFaceEqualizerArrow M 0) (spaceFaceEqualizerArrow M 1)
  adjunction : pullback ⊣ direct
  adjunction_zero (N : X.Modules) (M : SpaceFaceModuleSystem U) (f : pullback.obj N ⟶ M) :
    adjunction.homEquiv N M f ≫ eqToHom (directObject M) ≫
        equalizer.ι (spaceFaceEqualizerArrow M 0) (spaceFaceEqualizerArrow M 1) =
      (moduleTensorAdjunction ((spaceFaceDiagram U).obj (op (.mk 0))).hom).homEquiv _ _
        ((component (.mk 0)).inv.app N ≫ f.app (.mk 0))

/-- The canonical ordinary augmentation exists in the small-coefficient presentation.
Source: Stacks Project, spaces-simplicial.tex, Tags 09WF, 0D72 and 0D70,
with the injective-order-map index
(blueprint: lem-sfb-semisimplicial-ringed-total-category).

Proof: retain the generic total-site and derived assertions of
semisimplicial_ringed_total_category. For the enlarged algebraic-space specialization,
restrict each fibre module along smallEnlargedModuleEquivalence. Tensor pullback is
moduleTensorPullback by its chart-limit adjunction, and tensor associativity and
multiplication give precisely spaceFaceComposition and spaceFaceIdentity. Their tensor
normalizations prove the unit and associativity laws, so component tensor pullbacks
assemble into the displayed functor and component comparisons. The compatible-system
presentation of the total category is now SpaceFaceModuleSystem, with no change of
module universe. For any system M, take the equalizer of spaceFaceEqualizerArrow M 0
and spaceFaceEqualizerArrow M 1 in module sheaves. A map from any module N to this
equalizer is, by component adjunction, a degree-zero map whose two induced edge maps
agree. Pulling along every edge makes the vertex formula independent of the chosen
vertex in every degree. Composition then gives compatibility with every injection.
Conversely a map of systems gives these degree-zero data. These constructions are
mutually inverse and natural in N and M. Hence they define the ordinary direct-image
functor, its adjunction, and adjunction_zero. The equalizer is the ordinary ringed
augmentation direct image: the same compatible-section calculation is its right-adjoint
universal property. No hypercover or flatness hypothesis is used. -/
theorem space_face_total_augmentation {X : AlgebraicSpace S}
    (U : SimplicialObject (Over X)) : Nonempty (SpaceFaceAugmentationModel U) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
