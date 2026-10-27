module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Normalized infinitesimal cohomology data for formal functions

Source: Stacks Project, spaces-cohomology.tex, Tags 08AZ and 08B1.
(blueprint: def-sfb-space-formal-functions-data).

All models below retain their universal properties and their equations on chart sections.
They make no existence assertion. In particular a cohomological restriction cannot be
replaced by an unspecified linear map. Index n denotes the positive exponent n + 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

local instance (C : Type (u + 1)) [Category.{u} C] [Abelian C] :
    HasDerivedCategory.{u + 1} C := HasDerivedCategory.standard C
namespace AlgebraicGeometry.AlgebraicSpace.FormalFunctions

/-- The scheme base as its representable algebraic space.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
abbrev base (Y : Scheme.{u}) := schemeSpace (Over.mk (𝟙 Y))

/-- The given geometric point as a map of representable sheaves.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
def point {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y) :
    yoneda.obj (Over.mk y) ⟶ (base Y).obj.obj :=
  yoneda.map (Over.homMk y)

/-- The existing geometric stalk model, with its ring and module germs.
Source: Stacks 03G7 and 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
abbrev stalk {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) := SingleComplex.stalkModel y (point y)

/-- The geometric structure-sheaf stalk, not the ordinary Zariski local ring.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
abbrev ring {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) := (stalk y).ringCocone.pt

/-- Strict-local infinitesimal fibres, characterized by their actual pullback squares.
The map c is normalized by every affine pointed chart's colimit germ; transition
maps are normalized by both fibre-product projections.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
structure Geometry {Y : Scheme.{u}} (X : AlgebraicSpace Y) (f : X ⟶ base Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) where
  [localRing : IsLocalRing (ring y)]
  c : Spec (ring y) ⟶ Y
  canonical (V : SingleComplex.Neighbourhood (Over.mk y) (point y))
      (hV : IsAffine ((base Y).etaleForget.obj
        ((SingleComplex.neighbourhoodChart (x := point y)).obj V))) :
    Spec.map ((stalk y).ringCocone.ι.app (op V)) ≫
        (@Scheme.isoSpec _ hV).inv ≫
          ((SingleComplex.neighbourhoodChart (x := point y)).obj V).obj.left.hom = c
  space (n : ℕ) : AlgebraicSpace Y
  i (n : ℕ) : space n ⟶ X
  p (n : ℕ) : space n ⟶ schemeSpace (Over.mk
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ring y) ^ (n + 1)))) ≫ c))
  square (n : ℕ) : IsPullback (i n) (p n) f
    (ObjectProperty.homMk ⟨yoneda.map (Over.homMk
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ring y) ^ (n + 1)))) ≫ c))⟩)
  transition (n : ℕ) : space n ⟶ space (n + 1)
  transition_i (n : ℕ) : transition n ≫ i (n + 1) = i n
  transitionBase (n : ℕ) :
    Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (ring y) ^ (n + 1)))) ≫ c) ⟶
    Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (ring y) ^ ((n + 1) + 1)))) ≫ c)
  transitionBase_left (n : ℕ) : (transitionBase n).left =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (by omega) :
        IsLocalRing.maximalIdeal (ring y) ^ ((n + 1) + 1) ≤
          IsLocalRing.maximalIdeal (ring y) ^ (n + 1))))
  transition_p (n : ℕ) : (transition n).hom.hom ≫ (p (n + 1)).hom.hom =
    (p n).hom.hom ≫ yoneda.map (transitionBase n)

/-- The specified local ring's maximal ideal.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
abbrev Geometry.ideal {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) : Ideal (ring y) :=
  @IsLocalRing.maximalIdeal (ring y) _ D.localRing

/-- The finite-level coefficient ring.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
abbrev Geometry.quotient {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) (n : ℕ) :=
  ring y ⧸ D.ideal ^ (n + 1)

/-- The coefficient completion.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
abbrev Geometry.completion {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) := AdicCompletion (D.ideal) (ring y)

/-- The represented finite base, with its actual morphism to Y.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
def Geometry.finiteBase {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) (n : ℕ) : Over Y :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (D.ideal ^ (n + 1)))) ≫ D.c)

/-- Existing module global sections, with the completed ring acting by reduction.
Source: Stacks 08AZ, 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
abbrev Geometry.sections {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) (n : ℕ) :
    (D.space n).SmallModules ⥤ ModuleCat.{u} D.completion :=
  spaceAffineSections (D.finiteBase n) (Iso.refl _) (D.p n) ⋙
    ModuleCat.restrictScalars (AdicCompletion.evalₐ D.ideal (n + 1)).toRingHom

/-- The original module complex restricted to the fixed small model.
Source: Stacks 039Z, 079V (blueprint: def-sfb-space-formal-functions-data). -/
def complex {S : Scheme.{u}} {Z : AlgebraicSpace S} (K : CochainComplex Z.Modules ℤ) :=
  DerivedCategory.Q.obj ((smallModuleComplex Z).obj K)

/-- The canonical map from a complex to the derived image of its ordinary tensor pullback.
No exactness of tensor pullback is assumed. The map uses the existing derived adjunction
and its comparison with ordinary tensor pullback.
Source: Stacks 07A6, 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
def restriction {S : Scheme.{u}} {Z W : AlgebraicSpace S} (h : Z ⟶ W)
    (K : CochainComplex W.Modules ℤ) :
    complex K ⟶ (derivedDirectImage h).obj
      (complex (((moduleTensorPullback h).mapHomologicalComplex (.up ℤ)).obj K)) :=
  (spaceDerivedAdjunction h).unit.app (complex K) ≫
    (derivedDirectImage h).map (moduleOriginalPullbackCounit h K)

/-- A derived direct-image/sections compositor together with its ordinary compositor.
The equation on all K-injective complexes fixes the derived comparison uniquely by
right derivation; the ordinary comparison is normalized separately on chart sections.
Source: Stacks 0D6E, 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
structure Composition {S : Scheme.{u}} {Z W : AlgebraicSpace S} (h : Z ⟶ W)
    {R T : Type u} [CommRing R] [CommRing T]
    (G : W.SmallModules ⥤ ModuleCat.{u} R) [G.Additive]
    (H : Z.SmallModules ⥤ ModuleCat.{u} T) [H.Additive]
    (E : ModuleCat.{u} T ⥤ ModuleCat.{u} R) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] where
  ordinary : smallModuleDirectImage h ⋙ G ≅ H ⋙ E
  derived : derivedDirectImage h ⋙ G.rightDerivedFunctor ≅
    H.rightDerivedFunctor ⋙ E.mapDerivedCategory
  normalized (I : CochainComplex Z.SmallModules ℤ) [I.IsKInjective] :
    spaceRightDerivedComplexUnit G
        (((smallModuleDirectImage h).mapHomologicalComplex (.up ℤ)).obj I) ≫
      G.rightDerivedFunctor.map (spaceRightDerivedComplexUnit (smallModuleDirectImage h) I) ≫
      derived.hom.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app I) ≫
      E.mapDerivedCategoryFactors.inv.app
        ((H.mapHomologicalComplex (.up ℤ)).obj I) ≫
      E.mapDerivedCategory.map (spaceRightDerivedComplexUnit H I)

/-- The existing small-model geometric stalk functor.
Source: Stacks 03G7 (blueprint: def-sfb-space-formal-functions-data). -/
abbrev smallStalk {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) := SingleComplex.stalk y (point y)

/-- Forget only the completion's additional scalars.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
abbrev Geometry.scalars {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) := ModuleCat.restrictScalars (algebraMap (ring y) D.completion)

/-- A finite-fibre chart lies over the canonical map from the strict local spectrum.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
def Geometry.Compatible {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) (n : ℕ)
    (V : SingleComplex.Neighbourhood (Over.mk y) (point y))
    (hV : IsAffine ((base Y).etaleForget.obj
      ((SingleComplex.neighbourhoodChart (x := point y)).obj V)))
    (q : ModuleChart (D.i n ≫ f)
      ((SingleComplex.neighbourhoodChart (x := point y)).obj V)) : Prop :=
  q.hom.left.left = chartToScheme (D.finiteBase n) (D.p n) q.left ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.ideal ^ (n + 1)))) ≫
      Spec.map ((stalk y).ringCocone.ι.app (op V)) ≫ (@Scheme.isoSpec _ hV).inv

/-- All comparison data retain both chart and derived-unit normalizations.
Existence of this presentation is part of the formal-functions theorem, not a hypothesis.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
structure Cohomology {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) where
  stalkExact : PreservesFiniteLimits (smallStalk y) ∧ PreservesFiniteColimits (smallStalk y)
  stalkComposition (n : ℕ) : Composition (D.i n ≫ f) (smallStalk y) (D.sections n) D.scalars
  stalk_normalized (n : ℕ) (M : (D.space n).SmallModules)
      (V : SingleComplex.Neighbourhood (Over.mk y) (point y))
      (hV : IsAffine ((base Y).etaleForget.obj
        ((SingleComplex.neighbourhoodChart (x := point y)).obj V)))
      (q : ModuleChart (D.i n ≫ f)
        ((SingleComplex.neighbourhoodChart (x := point y)).obj V))
      (_ : D.Compatible n V hV q)
      (s : ((moduleDirectImage (D.i n ≫ f)).obj
        ((D.space n).smallModuleEquivalence.inverse.obj M)).val.obj
          (op ((SingleComplex.neighbourhoodChart (x := point y)).obj V))) :
    spaceAffineSectionAt (D.finiteBase n) (Iso.refl _) (D.p n) M q.left
      (((stalkComposition n).ordinary.hom.app M)
        ((stalk y).modules.map
          ((base Y).smallModuleEquivalence.unitIso.hom.app
            ((moduleDirectImage (D.i n ≫ f)).obj
              ((D.space n).smallModuleEquivalence.inverse.obj M)))
          (((stalk y).germs _).app (op V) s))) =
    ((moduleDirectImageModel (D.i n ≫ f)).projection
      ((D.space n).smallModuleEquivalence.inverse.obj M) _).app (op q) s
  transitionComposition (n : ℕ) :
    Composition (D.transition n) (D.sections (n + 1)) (D.sections n) (𝟭 _)
  transition_normalized (n : ℕ) (M : (D.space n).SmallModules)
      (V : (D.space (n + 1)).EtaleSite) (q : ModuleChart (D.transition n) V)
      (s : (D.sections (n + 1)).obj ((smallModuleDirectImage (D.transition n)).obj M)) :
    ((moduleDirectImageModel (D.transition n)).projection
      ((D.space n).smallModuleEquivalence.inverse.obj M) V).app (op q)
      ((((D.space (n + 1)).smallModuleEquivalence.unitIso.inv.app
        ((moduleDirectImage (D.transition n)).obj
          ((D.space n).smallModuleEquivalence.inverse.obj M))).val.app (op V))
        (spaceAffineSectionAt (D.finiteBase (n + 1)) (Iso.refl _) (D.p (n + 1))
          ((smallModuleDirectImage (D.transition n)).obj M) V s)) =
    spaceAffineSectionAt (D.finiteBase n) (Iso.refl _) (D.p n) M q.left
      (((transitionComposition n).ordinary.hom.app M) s)

/-- The original degree-zero complex of the given module.
Source: Stacks 079V (blueprint: def-sfb-space-formal-functions-data). -/
abbrev single {S : Scheme.{u}} {Z : AlgebraicSpace S} (F : Z.Modules) :=
  (CochainComplex.singleFunctor Z.Modules 0).obj F

/-- The actual finite-level tensor-restriction complex.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
abbrev Geometry.finiteComplex {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) (F : X.Modules) (n : ℕ) :=
  ((moduleTensorPullback (D.i n)).mapHomologicalComplex (.up ℤ)).obj (single F)

/-- The specified module-derived direct-image geometric stalk in degree q.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
def source {Y : Scheme.{u}} {X : AlgebraicSpace Y} (f : X ⟶ base Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : X.Modules) (q : ℕ) :=
  (smallStalk y).obj ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
    ((derivedDirectImage f).obj (complex (single F))))

/-- Finite-fibre cohomology is derived module global sections, with completed scalars.
Source: Stacks 08AZ, 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
def Geometry.finite {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) (F : X.Modules) (n q : ℕ) :=
  (DerivedCategory.homologyFunctor _ (q : ℤ)).obj
    ((D.sections n).rightDerivedFunctor.obj (complex (D.finiteComplex F n)))

/-- The canonical cohomological map from the higher-image stalk to a finite fibre.
Direct-image composition is the right-adjoint conjugate of the canonical derived pullback
composition through the normalized derived adjunctions.
Source: Stacks 08B1, 0D6E (blueprint: def-sfb-space-formal-functions-data). -/
def Cohomology.map {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    {D : Geometry X f y} (C : Cohomology D) (F : X.Modules) (n q : ℕ) :
    source f y F q ⟶ D.scalars.obj (D.finite F n q) :=
  letI := C.stalkExact.1
  letI := C.stalkExact.2
  ((smallStalk y).rightDerivedFunctorHomologyFunctorIso (q : ℤ)).hom.app _ ≫
    (DerivedCategory.homologyFunctor _ (q : ℤ)).map
      ((smallStalk y).rightDerivedFunctor.map
        ((derivedDirectImage f).map (restriction (D.i n) (single F)) ≫
          (conjugateIsoEquiv
            ((spaceDerivedAdjunction f).comp (spaceDerivedAdjunction (D.i n)))
            (spaceDerivedAdjunction (D.i n ≫ f))
            (spaceDerivedPullbackComp f (D.i n))).hom.app _) ≫
        (C.stalkComposition n).derived.hom.app _) ≫
    (D.scalars.mapDerivedCategoryHomologyFunctorIso (q : ℤ)).inv.app _

/-- Tensor transitivity identifies the restriction of F_(n+1) with F_n.
Source: Stacks 08B1, tensor formula in its proof
(blueprint: def-sfb-space-formal-functions-data). -/
def Geometry.tensorTransition {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    (D : Geometry X f y) (F : X.Modules) (n : ℕ) :
    ((moduleTensorPullback (D.transition n)).mapHomologicalComplex (.up ℤ)).obj
      (D.finiteComplex F (n + 1)) ≅ D.finiteComplex F n :=
  (Functor.mapHomologicalComplexCompIso
    (moduleTensorComposition (D.transition n) (D.i (n + 1)) ≪≫
      eqToIso (congrArg moduleTensorPullback (D.transition_i n))) (.up ℤ)).app (single F)

/-- The actual restriction transition on finite-fibre cohomology.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
def Cohomology.transition {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    {D : Geometry X f y} (C : Cohomology D) (F : X.Modules) (n q : ℕ) :
    D.finite F (n + 1) q ⟶ D.finite F n q :=
  (DerivedCategory.homologyFunctor _ (q : ℤ)).map
    ((D.sections (n + 1)).rightDerivedFunctor.map
      (restriction (D.transition n) (D.finiteComplex F (n + 1)) ≫
        (derivedDirectImage (D.transition n)).map
          (DerivedCategory.Q.map ((smallModuleComplex (D.space n)).map
            (D.tensorTransition F n).hom))) ≫
      (C.transitionComposition n).derived.hom.app _) ≫
    ((𝟭 (ModuleCat.{u} D.completion)).mapDerivedCategoryHomologyFunctorIso
      (q : ℤ)).inv.app _

/-- The inverse system indexed by positive exponents n+1.
Source: Stacks 08B1 (blueprint: def-sfb-space-formal-functions-data). -/
def Cohomology.tower {Y : Scheme.{u}} {X : AlgebraicSpace Y} {f : X ⟶ base Y}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    {D : Geometry X f y} (C : Cohomology D) (F : X.Modules) (q : ℕ) :
    ℕᵒᵖ ⥤ ModuleCat.{u} D.completion :=
  Functor.ofOpSequence (X := fun n ↦ D.finite F n q) (fun n ↦ C.transition F n q)

end AlgebraicGeometry.AlgebraicSpace.FormalFunctions
