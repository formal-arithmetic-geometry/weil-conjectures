/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Algebra.Homology.RingedSiteGlobalHomIdentification
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.RingedTensorSquarePresentation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Direct image on global derived Hom

Source: Stacks Project, Tags 0B6C, 0B6D, 0D6E, 0D6H and 08JA
(blueprint: lem-sfb-ringed-site-global-hom-direct-image).

Global sections are compatible families, so a final object of the presented site
is unnecessary. Their scalar action comes from the specified global ring sections.
-/

@[expose] public noncomputable section
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedVariables false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedSiteGlobalHomDirectImage
open RingedSiteScalarGlobalSections RingedSiteGlobalHomIdentification
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) (A : Type u) [CommRing A]
  (s : A →+* Scalars R)
  [HasDerivedCategory.{w} (Modules R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]

attribute [local irreducible] derivedInternalHomOfUniverses Functor.rightDerivedFunctor

/-- The complex-level counit computation map of the supplied derived pullback.
Source: Stacks 0D6D (blueprint: lem-sfb-ringed-site-global-hom-direct-image). -/
def pullbackComputation {Y X : SheafOfModules.RingedTensorCorner.{u, w}}
    (e : SheafOfModules.RingedTensorEdge Y X)
    (M : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) ℤ) :
    e.left.obj (DerivedCategory.Q.obj M) ⟶
      DerivedCategory.Q.obj ((e.pullback.mapHomologicalComplex (.up ℤ)).obj M) :=
  e.left.map ((DerivedCategory.quotientCompQhIso _).inv.app M) ≫
    e.epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj M) ≫
    DerivedCategory.Qh.map ((e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom.app M) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app _

/-- The tensor-of-counits relative cup, with the canonical tensor comparison.
Source: Stacks 0B6C (blueprint: lem-sfb-ringed-site-global-hom-direct-image). -/
def cup {Y X : SheafOfModules.RingedTensorCorner.{u, w}}
    (e : SheafOfModules.RingedTensorEdge Y X)
    (a : SheafOfModules.RingedTensorModel Y) (b : SheafOfModules.RingedTensorModel X)
    (E F : DerivedCategory (ringedSiteModules.{u, u, u, u}
      ((sheafCompose X.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X.ring))) :
    Y.tensor.obj (e.right.obj E, e.right.obj F) ⟶ e.right.obj (X.tensor.obj (E, F)) :=
  (e.derivedAdjunction.homEquiv _ _)
    ((e.tensorComparison a b).hom.app (e.right.obj E, e.right.obj F) ≫
      X.tensor.map (e.derivedAdjunction.counit.app E, e.derivedAdjunction.counit.app F))

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  (B : Sheaf K CommRingCat.{u}) [HasDerivedCategory.{w} (Modules B)]

/-- The fixed closed tensor models and a derived pullback edge on the two sites.
Source: Stacks 07A4, 08J9 (blueprint: lem-sfb-ringed-site-global-hom-direct-image). -/
structure TensorData where
  sourceClosed : WeilConjectures.CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u, u, u, w} J R)
  targetClosed : WeilConjectures.CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u, u, u, w} K B)
  sourceModel : WeilConjectures.CoefficientTensorModels.{u, u, u, w} J R sourceClosed
  targetModel : WeilConjectures.CoefficientTensorModels.{u, u, u, w} K B targetClosed
  edge : SheafOfModules.RingedTensorEdge (corner B targetClosed) (corner R sourceClosed)

/-- The comparison data, including representative normalizations. Every map is
fixed either by the derived universal property or by the stated evaluation formula.
Source: Stacks 0B6C, 0B6D, 0D6E, 0D6H, 08JA
(blueprint: lem-sfb-ringed-site-global-hom-direct-image). -/
structure Presentation
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (t : A →+* Scalars B) (g : TensorData R B) where
  sourceScalars : A →+* Scalars R
  pushforwardIso : g.edge.pushforward ≅ f.modules
  sectionsIso : g.edge.pushforward ⋙ sections B A t ≅ sections R A sourceScalars

/-- Normalization of the supplied direct-image presentation on geometry and sections.
Source: Stacks 03D7, 0D6H (blueprint: lem-sfb-ringed-site-global-hom-direct-image). -/
def PresentationValid
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (t : A →+* Scalars B) (g : TensorData R B) (p : Presentation R A B f t g) : Prop :=
  (HEq g.edge.inverse f.inverse) ∧
  (HEq g.edge.direct f.direct) ∧
  (HEq g.edge.adjunction f.adj) ∧
  (HEq
    (g.edge.algebraic.ringUnderlying.hom ≫
      (sheafCompose J (forget CommRingCat)).map g.edge.ringMap) f.ringMap) ∧
  (∀ (M : Modules B) (N : Modules R) (v : g.edge.pullback.obj M ⟶ N),
    HEq ((SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).map
        ((g.edge.moduleAdjunction.homEquiv M N v) ≫ p.pushforwardIso.hom.app N) ≫
          f.underlying.hom.app N)
      (g.edge.adjunction.homEquiv _ _ (g.edge.insertion M ≫
        (SheafOfModules.toSheaf _ ⋙ sheafCompose J (forget AddCommGrpCat)).map v))) ∧
  (∀ (a : A) (U : Cᵒᵖ)
    (x : (f.inverse.obj (⊤_ (Sheaf K (Type u)))).obj.obj U),
    (f.inverse.map (scalarOn B A t a (⊤_ _)) ≫ f.ringMap).hom.app U x =
      (p.sourceScalars a).val U) ∧
  (∀ (M : Modules R)
    (x : (sections B A t).obj (g.edge.pushforward.obj M)),
    (f.adj.homEquiv _ _).symm
        (sectionOn B A t _ x (⊤_ _) ≫
          (SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).map
            (p.pushforwardIso.hom.app M) ≫ f.underlying.hom.app M) =
      sectionOn R A p.sourceScalars M (p.sectionsIso.hom.app M x)
        (f.inverse.obj (⊤_ _)))

attribute [local irreducible] sections sectionSubmodule scalarAt

/-- The canonical right-derived computation map transported to a specified model.
Source: Stacks 0D6E (blueprint: lem-sfb-ringed-site-global-hom-direct-image). -/
def rightUnit (F : Modules R ⥤ Modules B) [F.Additive]
    (U : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules B))
    (e : U ≅ F.rightDerivedFunctor) (M : Complexes R) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj M) ⟶
      U.obj (DerivedCategory.Q.obj M) :=
  computationUnit R F M ≫ e.inv.app (DerivedCategory.Q.obj M)

/-- The derived-unit composite fixing inverse Leray, written before specializing
its functors to the chosen ringed-topos presentation.
Source: Stacks 0D6E, 0D6H (blueprint: lem-sfb-ringed-site-global-hom-direct-image). -/
def lerayUnitMap (t : A →+* Scalars B)
    (F : Modules R ⥤ Modules B) [F.Additive]
    (U : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules B))
    (e : U ≅ F.rightDerivedFunctor) (a : F ⋙ sections B A t ≅ sections R A s)
    (M : Complexes R) :
    DerivedCategory.Q.obj (((sections R A s).mapHomologicalComplex (.up ℤ)).obj M) ⟶
      (derivedSections B A t).obj (U.obj (DerivedCategory.Q.obj M)) :=
  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.inv (.up ℤ)).app M) ≫
    DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ sections B A t))
        (.up ℤ)).inv.app M) ≫
    computationUnit B (sections B A t) ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
    (derivedSections B A t).map (rightUnit R B F U e M)

attribute [local irreducible] tensorModel cup representativeMap cocycleMorphism
  pullbackComputation lerayUnitMap rightUnit

/-- The derived comparison attached to a normalized presentation of the given morphism.
Source: Stacks 0B6C, 0B6D, 0D6E, 0D6H, 08JA
(blueprint: lem-sfb-ringed-site-global-hom-direct-image). -/
structure DerivedData
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (t : A →+* Scalars B) (g : TensorData R B) (p : Presentation R A B f t g) where
  [pushAdditive : g.edge.pushforward.Additive]
  [rShift : g.edge.right.CommShift ℤ]
  rightIso : g.edge.right ≅ g.edge.pushforward.rightDerivedFunctor
  rightIsoShift : NatTrans.CommShift rightIso.hom ℤ
  counit_normalization : ∀ (I : Complexes R),
    g.edge.left.map (rightUnit R B g.edge.pushforward g.edge.right rightIso I) ≫
      g.edge.derivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
        pullbackComputation g.edge ((g.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex g.edge.moduleAdjunction.counit (.up ℤ)).app I)
  leray : g.edge.right ⋙ derivedSections B A t ≅ derivedSections R A p.sourceScalars
  leray_normalization : ∀ (M : Complexes R),
    computationUnit R (sections R A p.sourceScalars) M ≫
        leray.inv.app (DerivedCategory.Q.obj M) =
      lerayUnitMap R A p.sourceScalars B t g.edge.pushforward g.edge.right
        rightIso p.sectionsIso M

/-- The evaluation and global comparison, with the all-degree cocycle normalization.
Source: Stacks 0B6D, 08JA (blueprint: lem-sfb-ringed-site-global-hom-direct-image). -/
structure Comparison
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (t : A →+* Scalars B) (g : TensorData R B) (p : Presentation R A B f t g)
    (d : DerivedData R A B f t g p) where
  theta : derivedInternalHomOfUniverses.{u, u, u, w} J R ⋙ g.edge.right ⟶
    (g.edge.right.op.prod g.edge.right) ⋙ derivedInternalHomOfUniverses.{u, u, u, w} K B
  theta_formula : ∀ (M N : DerivedCategory (Modules R)),
    theta.app (op M, N) = g.targetClosed.transpose _ (g.edge.right.obj M) (g.edge.right.obj N)
      (cup g.edge (tensorModel B g.targetClosed g.targetModel)
        (tensorModel R g.sourceClosed g.sourceModel) _ M ≫
          g.edge.right.map (g.sourceClosed.evaluation M N))
  comparison : globalHom R A p.sourceScalars ⟶
    (g.edge.right.op.prod g.edge.right) ⋙ globalHom B A t
  comparison_formula : ∀ (M N : DerivedCategory (Modules R)),
    comparison.app (op M, N) =
      d.leray.inv.app ((derivedInternalHomOfUniverses.{u, u, u, w} J R).obj (op M, N)) ≫
        (derivedSections B A t).map (theta.app (op M, N))
  sourceIdentification : HomIdentification R A p.sourceScalars
  targetIdentification : HomIdentification B A t
  cohomology_formula : ∀ (M N : DerivedCategory (Modules R)) (n : ℤ)
    (v : M ⟶ N⟦n⟧),
    targetIdentification.equiv (g.edge.right.obj M) (g.edge.right.obj N) n
      (((DerivedCategory.homologyFunctor (ModuleCat A) n).map (comparison.app (op M, N)))
        ((sourceIdentification.equiv M N n).symm v)) =
      g.edge.right.map v ≫
        (@Functor.commShiftIso _ _ _ _ g.edge.right ℤ _ _ _ d.rShift n).hom.app N

/-- Every morphism of small ringed topoi induces the canonical natural map of global
derived Hom complexes, whose action in every integer degree is derived direct image.
There are no boundedness, flatness or final-object assumptions.

Source: Stacks Project, Tags 0B6C, 0B6D, 0D6E, 0D6H and 08JA
(blueprint: lem-sfb-ringed-site-global-hom-direct-image).

Proof: choose the canonical K-flat derived pullback and K-injective right derived
pushforward, with their representative-normalized adjunction. The tensor-of-counits
adjunct is the relative cup. Transpose its composite with direct image of evaluation
to obtain theta; its formula proves naturality. Apply unbounded Leray to composition
with the global-sections morphism to the punctual ringed topos (A); the ordinary
sections identification fixes Leray by its derived-unit equation. Define the global
comparison by inverse Leray followed by derived sections of theta. For a K-flat P
and a K-injective resolution I of M, the Hom complex Hom(P,I) is K-injective and its
sections are the external Hom complex, with the product projections specified above.
Its degree-n cocycles yield exactly Q(P) -> Q(M)[n]. Apply the adjunction to the
evaluation pairing for such a cocycle. Naturality of the counit reduces the resulting
map to direct image of that morphism. Counit/shift compatibility supplies precisely
the displayed canonical shift comparison, for every positive or negative n.
-/
theorem globalHomDirectImage
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (t : A →+* Scalars B) : ∃ g : TensorData R B, ∃ p : Presentation R A B f t g,
      PresentationValid R A B f t g p ∧ ∃ d : DerivedData R A B f t g p,
      Nonempty (Comparison R A B f t g p d) := by
  sorry

end CategoryTheory.RingedSiteGlobalHomDirectImage
