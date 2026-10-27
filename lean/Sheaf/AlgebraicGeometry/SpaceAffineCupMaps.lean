module

public import Sheaf.AlgebraicGeometry.SpaceAffineBaseHigherImageSections
public import Sheaf.CategoryTheory.RingedSiteModuleCupProduct
public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat

/-! # Canonical affine-base cup and exchange maps

Source: Stacks Project, Cohomology on Sites, Tags 0B6C, 0FPN and 0H9A
(blueprint: def-sfb-space-affine-cup-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules
namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The existing small ringed model and its existing derived tensor.
Source: Stacks 039Z, 0B6C (blueprint: def-sfb-space-affine-cup-maps). -/
def cupCorner (X : AlgebraicSpace S) :
    RingedTensorCorner.{u, u} where
  site := X.SmallEtaleModel
  topology := X.smallEtaleModelTopology
  ring := X.smallStructureSheaf
  tensor := X.derivedDualityModel.closed.tensor

/-- Restrict the recorded tensor model to flat-term K-flat representatives.
Source: Stacks 06YU (blueprint: def-sfb-space-affine-cup-maps). -/
def cupTensorModel (X : AlgebraicSpace S) :
    RingedTensorModel (cupCorner.{u} X) :=
  { representative := Functor.isoWhiskerLeft
      (({
        obj := fun P ↦ ⟨P.obj,
          (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
        map := fun a ↦ ObjectProperty.homMk a.hom } :
        ObjectProperty.FullSubcategory (cupCorner.{u} X).mateFlat ⥤
          ObjectProperty.FullSubcategory
            (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
              (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf))).prod
        ({
        obj := fun P ↦ ⟨P.obj,
          (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
        map := fun a ↦ ObjectProperty.homMk a.hom } :
        ObjectProperty.FullSubcategory (cupCorner.{u} X).mateFlat ⥤
          ObjectProperty.FullSubcategory
            (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
              (J := X.smallEtaleModelTopology) (R := X.smallStructureSheaf))))
        X.derivedDualityModel.models.comparison }

/-- Compute the native global-section functor on an injective resolution.
Source: Stacks 03FD (blueprint: def-sfb-space-affine-cup-maps). -/
def cupNativeResolutionIso (X : AlgebraicSpace S) (M : X.SmallModules)
    (I : InjectiveResolution M) (q : ℕ) :=
  letI := RingedSiteCup.globalSections_additive (cupCorner X)
  I.isoRightDerivedObj (RingedSiteCup.globalSections (cupCorner X)) q

/-- The existing ordinary tensor.
Source: Stacks 03EK (blueprint: def-sfb-space-affine-cup-maps). -/
abbrev cupTensor (X : AlgebraicSpace S) (F G : X.SmallModules) :=
  (SheafOfModules.monoidalCategory X.smallStructureSheaf).tensorObj F G

/-- The existing cohomology functor.
Source: Stacks 079V (blueprint: def-sfb-space-affine-cup-maps). -/
abbrev cupH (X : AlgebraicSpace S) (q : ℤ) :=
  DerivedCategory.homologyFunctor X.SmallModules q

/-- The tensor of counits defines the canonical relative derived cup.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-cup-maps). -/
def spaceRelativeDerivedCup {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (K L : X.DerivedModules) :
    Y.derivedDualityModel.closed.tensor.obj
        ((derivedDirectImage f).obj K, (derivedDirectImage f).obj L) ⟶
      (derivedDirectImage f).obj (X.derivedDualityModel.closed.tensor.obj (K, L)) :=
  (spaceDerivedAdjunction f).homEquiv _ _
    ((moduleDerivedPullbackTensor f).hom.app _ ≫
      X.derivedDualityModel.closed.tensor.map
        (Prod.mkHom ((spaceDerivedAdjunction f).counit.app K)
          ((spaceDerivedAdjunction f).counit.app L)))

/-- Relative cup in classical right derived functors.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-cup-maps). -/
def spaceModuleCup {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F G : X.SmallModules) (a b : ℕ) :
    cupTensor Y (((smallModuleDirectImage f).rightDerived a).obj F)
      (((smallModuleDirectImage f).rightDerived b).obj G) ⟶
      ((smallModuleDirectImage f).rightDerived (a + b)).obj (cupTensor X F G) :=
  (SheafOfModules.monoidalCategory Y.smallStructureSheaf).tensorHom
      ((smallModuleDirectImage f).homologyRightDerivedFunctorObjSingleFunctorIso F a).inv
      ((smallModuleDirectImage f).homologyRightDerivedFunctorObjSingleFunctorIso G b).inv ≫
    RingedSiteCup.cohomologyPairing (cupCorner Y) (cupTensorModel Y)
      ((derivedDirectImage f).obj ((DerivedCategory.singleFunctor _ 0).obj F))
      ((derivedDirectImage f).obj ((DerivedCategory.singleFunctor _ 0).obj G)) a b ≫
    (cupH Y ((a : ℤ) + (b : ℤ))).map
      (spaceRelativeDerivedCup f ((DerivedCategory.singleFunctor _ 0).obj F)
        ((DerivedCategory.singleFunctor _ 0).obj G) ≫
        (derivedDirectImage f).map
          (RingedSiteCup.tensorAugmentation (cupCorner X) (cupTensorModel X) F G)) ≫
    (eqToIso (congrArg (fun n : ℤ ↦ (cupH Y n).obj
      ((derivedDirectImage f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (cupTensor X F G))))
      (Nat.cast_add a b).symm)).hom ≫
    ((smallModuleDirectImage f).homologyRightDerivedFunctorObjSingleFunctorIso _ (a + b)).hom

/-- Affine scalar cohomology, derived in all module sheaves.
Source: Stacks 08EX (blueprint: def-sfb-space-affine-cup-maps). -/
abbrev affineCupH (A : Type u) [CommRing A] (Y : Over S)
    (e : Y.left ≅ Spec (.of A)) (X : AlgebraicSpace S)
    (f : X ⟶ schemeSpace Y) (q : ℕ) := (affineScalarSections A Y e X f).rightDerived q

section Affine
variable (A : Type u) [CommRing A] (Y : Over S) (e : Y.left ≅ Spec (.of A))
  (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)

/-- Exact scalar restriction from global functions to the affine base.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-cup-maps). -/
abbrev cupScalarRestriction := ModuleCat.restrictScalars (affineGlobalScalar A Y e X f)

/-- The kernel and homology normalization for exact scalar restriction.
Source: Stacks 03FD (blueprint: def-sfb-space-affine-cup-maps). -/
def CupScalarSpec (d : ∀ q : ℕ, affineCupH A Y e X f q ≅
    (RingedSiteCup.globalSections (cupCorner X)).rightDerived q ⋙
      cupScalarRestriction A Y e X f) : Prop :=
  ∀ (q : ℕ) (M : X.SmallModules) (I : InjectiveResolution M),
    ∃ c : (cupScalarRestriction A Y e X f).obj
        ((((RingedSiteCup.globalSections (cupCorner X)).mapHomologicalComplex
          (.up ℕ)).obj I.cocomplex).cycles q) ⟶
      (affineBaseSectionsComplex A Y e X f I.cocomplex).cycles q,
      c ≫ (affineBaseSectionsComplex A Y e X f I.cocomplex).iCycles q =
        (cupScalarRestriction A Y e X f).map
          ((((RingedSiteCup.globalSections (cupCorner X)).mapHomologicalComplex
            (.up ℕ)).obj I.cocomplex).iCycles q) ∧
      c ≫ (affineBaseSectionsComplex A Y e X f I.cocomplex).homologyπ q ≫
        (I.isoRightDerivedObj (affineScalarSections A Y e X f) q).inv ≫ (d q).hom.app M =
      (cupScalarRestriction A Y e X f).map
        (((((RingedSiteCup.globalSections (cupCorner X)).mapHomologicalComplex
          (.up ℕ)).obj I.cocomplex).homologyπ q) ≫ (cupNativeResolutionIso X M I q).inv)

/-- Exact restriction supplies a unique resolution-normalized comparison.
Source: Stacks 03FD (blueprint: def-sfb-space-affine-cup-maps).
Proof: global sections followed by restriction of scalars is the recorded affine
sections functor. Apply it to an injective resolution. Exact restriction preserves
cycles, boundaries and homology, giving c and d with the displayed equations.
Resolution comparisons prove naturality and independence. The cycle inclusion is
monic and the homology quotient is epic, proving uniqueness. -/
theorem cupScalarComparison_existsUnique : ∃! d, CupScalarSpec A Y e X f d := by
  sorry

/-- The uniquely resolution-normalized scalar comparison.
Source: Stacks 03FD (blueprint: def-sfb-space-affine-cup-maps). -/
def cupScalarComparison := (cupScalarComparison_existsUnique A Y e X f).choose

/-- The recorded global cup, restricted to the affine base scalars.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-cup-maps). -/
def affineGlobalCup (F G : X.SmallModules) (a b : ℕ)
    (x : (affineCupH A Y e X f a).obj F) (y : (affineCupH A Y e X f b).obj G) :
    (affineCupH A Y e X f (a + b)).obj (cupTensor X F G) :=
  (cupScalarComparison A Y e X f (a + b)).inv.app _
    ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (RingedSiteCup.globalSections (cupCorner X)) _ (a + b)).hom
      (RingedSiteCup.globalModuleCup (cupCorner X) (cupTensorModel X) F G a b
        (TensorProduct.tmul (RingedSiteCup.scalars (cupCorner X))
          ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
            (RingedSiteCup.globalSections (cupCorner X)) F a).inv
            ((cupScalarComparison A Y e X f a).hom.app F x))
          ((Functor.homologyRightDerivedFunctorObjSingleFunctorIso
            (RingedSiteCup.globalSections (cupCorner X)) G b).inv
            ((cupScalarComparison A Y e X f b).hom.app G y)))))

/-- Tensor two compatible sections, using the ordinary sheaf tensor.
Source: Stacks 0FPN (blueprint: def-sfb-space-affine-cup-maps). -/
def affineSectionTensor (F G : X.SmallModules)
    (x : (affineScalarSections A Y e X f).obj F)
    (y : (affineScalarSections A Y e X f).obj G) :
    (affineScalarSections A Y e X f).obj (cupTensor X F G) :=
  ((SheafOfModules.monoidalCategory X.smallStructureSheaf).leftUnitor
      (SheafOfModules.unit X.smallStructureRings)).inv ≫
    (SheafOfModules.monoidalCategory X.smallStructureSheaf).tensorHom x y

/-- The recorded affine edge normalization, extended to all module sheaves.
Source: Stacks 08EX, 0D6H (blueprint: def-sfb-space-affine-cup-maps). -/
def CupEdgeSpec (d : ∀ q : ℕ, affineCupH A Y e X f q ⟶
    (smallModuleDirectImage f).rightDerived q ⋙
      affineScalarSections A Y e (schemeSpace Y) (𝟙 _)) : Prop :=
  (∀ (q : ℕ) (M : X.SmallModules) (I : InjectiveResolution M),
    ∃ c : (affineScalarSections A Y e (schemeSpace Y) (𝟙 _)).obj
        ((affineBaseImageComplex Y X f I.cocomplex).cycles q) ⟶
      (affineBaseSectionsComplex A Y e X f I.cocomplex).cycles q,
      c ≫ (affineBaseSectionsComplex A Y e X f I.cocomplex).iCycles q =
        (affineScalarSections A Y e (schemeSpace Y) (𝟙 _)).map
          ((affineBaseImageComplex Y X f I.cocomplex).iCycles q) ≫
            (affineSectionsComposition A Y e X f).inv.app (I.cocomplex.X q) ∧
      c ≫ (affineBaseSectionsComplex A Y e X f I.cocomplex).homologyπ q ≫
        (I.isoRightDerivedObj (affineScalarSections A Y e X f) q).inv ≫ (d q).app M ≫
        (affineScalarSections A Y e (schemeSpace Y) (𝟙 _)).map
          (I.isoRightDerivedObj (smallModuleDirectImage f) q).hom =
        (affineScalarSections A Y e (schemeSpace Y) (𝟙 _)).map
          ((affineBaseImageComplex Y X f I.cocomplex).homologyπ q)) ∧
  (∀ (hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hqs : IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom)) (q : ℕ) (M : X.QCoh),
    (d q).app (X.smallModuleRestriction.obj M.obj) =
      ((exists_affineBaseHigherImageSections_iso A Y e X f hqc hqs).choose q).hom.app M)

/-- Existence and uniqueness of the cocycle-normalized Leray edge.
Source: Stacks 0D6H, 08EX (blueprint: def-sfb-space-affine-cup-maps).
Proof: left exact sections preserve cycles. The ordinary compositor gives c, which
is unique by its monic cycle inclusion. The map to sections of image homology
kills global boundaries, hence descends through the homology cokernel to d.
Resolution comparisons give naturality and independence. The same cokernel gives
uniqueness. Restricted to QCoh, this formula is precisely the normalization of
exists_affineBaseHigherImageSections_iso, so uniqueness identifies those maps. -/
theorem cupEdge_existsUnique : ∃! d, CupEdgeSpec A Y e X f d := by
  sorry

/-- Theta, extending the dependency's identical normalized edge to all inputs.
Source: Stacks 08EX (blueprint: def-sfb-space-affine-cup-maps). -/
def affineCupEdge := (cupEdge_existsUnique A Y e X f).choose
end Affine

section Pullback
variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Scalar/cocycle pullback fixed on every flat K-flat representative.
Source: Stacks 07A7, 0BKV (blueprint: def-sfb-space-affine-cup-maps). -/
def CupPullbackSpec (K : Y.DerivedModules) (q : ℤ)
    (r : (smallModuleTensorPullback f).obj ((cupH Y q).obj K) ⟶
      (cupH X q).obj ((spaceDerivedPullback f).obj K)) : Prop :=
  ∀ (P : CochainComplex Y.SmallModules ℤ) (_hP : SingleComplex.FlatKFlat Y P)
    (i : DerivedCategory.Q.obj P ≅ K),
    ∃ z : (smallModuleTensorPullback f).obj (P.cycles q) ⟶
      (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj P).cycles q,
      z ≫ (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj P).iCycles q =
        (smallModuleTensorPullback f).map (P.iCycles q) ∧
      (smallModuleTensorPullback f).map
          (P.homologyπ q ≫ (DerivedCategory.homologyFunctorFactors _ q).inv.app P ≫
            (cupH Y q).map i.hom) ≫ r ≫
          (cupH X q).map
            ((spaceDerivedPullback f).map i.inv ≫ (spaceDerivedPullbackCounit f).app P) =
        z ≫ (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ)).obj P).homologyπ q ≫
          (DerivedCategory.homologyFunctorFactors _ q).inv.app _

/-- The uniquely scalar/cocycle-normalized ordinary comparison exists.
Source: Stacks 07A7, 0BKV (blueprint: def-sfb-space-affine-cup-maps).
Proof: pull back the cycles inclusion; it lands in pulled-back cycles. Boundaries
map to boundaries. Right exactness descends the resulting map through the homology
quotient. The derived counit is invertible on flat K-flat representatives.
Transport by that counit and i. Refinements, homotopies and localization give
independence. Monic cycle inclusions and epic pulled homology quotients give
uniqueness. This does not assert that pullback is exact or the map invertible. -/
theorem cupPullback_existsUnique (K : Y.DerivedModules) (q : ℤ) :
    ∃! r, CupPullbackSpec f K q r := by
  sorry

/-- The ordinary pullback to cohomology comparison.
Source: Stacks 07A7 (blueprint: def-sfb-space-affine-cup-maps). -/
def cupPullback (K : Y.DerivedModules) (q : ℤ) := (cupPullback_existsUnique f K q).choose

/-- The canonical augmentation to ordinary pullback of a degree-zero coefficient.
Source: Stacks 07A7 (blueprint: def-sfb-space-affine-cup-maps). -/
def cupPullbackAugmentation (F : Y.SmallModules) :
    (spaceDerivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((smallModuleTensorPullback f).obj F) :=
  (spaceDerivedPullback f).map ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app F) ≫
    (spaceDerivedPullbackCounit f).app ((CochainComplex.singleFunctor _ 0).obj F) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (smallModuleTensorPullback f) (.up ℤ) 0).hom.app F) ≫
    (DerivedCategory.singleFunctorIsoCompQ X.SmallModules 0).inv.app
      ((smallModuleTensorPullback f).obj F)
end Pullback

section Square
variable {X Y X' Y' : AlgebraicSpace S}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (h : X' ⟶ X) (k : X' ⟶ Y')
  (w : h ≫ f = k ≫ g)

/-- The pointwise square comparison of the already normalized derived pullbacks.
Source: Stacks 0D6D (blueprint: def-sfb-space-affine-cup-maps). -/
def cupSquareComparison (K : Y.DerivedModules) :
    (spaceDerivedPullback k).obj ((spaceDerivedPullback g).obj K) ⟶
      (spaceDerivedPullback h).obj ((spaceDerivedPullback f).obj K) :=
  (spaceDerivedPullbackComp g k).inv.app K ≫
    eqToHom (congrArg (fun t : X' ⟶ Y ↦
      (spaceDerivedPullback t).obj K) w.symm) ≫
    (spaceDerivedPullbackComp f h).hom.app K

/-- Canonical exchange, the counit mate of the fixed pullback-square comparison.
Source: Stacks 07A7 (blueprint: def-sfb-space-affine-cup-maps). -/
def cupDerivedExchange (K : X.DerivedModules) :
    (spaceDerivedPullback g).obj ((derivedDirectImage f).obj K) ⟶
      (derivedDirectImage k).obj ((spaceDerivedPullback h).obj K) :=
  (spaceDerivedAdjunction k).homEquiv _ _
    (cupSquareComparison f g h k w ((derivedDirectImage f).obj K) ≫
      (spaceDerivedPullback h).map ((spaceDerivedAdjunction f).counit.app K))

/-- The degree-q ordinary base-change map, including coefficient augmentation.
Source: Stacks 07A7 (blueprint: def-sfb-space-affine-cup-maps). -/
def cupModuleBaseChange (F : X.SmallModules) (q : ℕ) :
    (smallModuleTensorPullback g).obj (((smallModuleDirectImage f).rightDerived q).obj F) ⟶
      ((smallModuleDirectImage k).rightDerived q).obj ((smallModuleTensorPullback h).obj F) :=
  (smallModuleTensorPullback g).map
      ((smallModuleDirectImage f).homologyRightDerivedFunctorObjSingleFunctorIso F q).inv ≫
    cupPullback g ((derivedDirectImage f).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) q ≫
    (cupH Y' q).map
      (cupDerivedExchange f g h k w ((DerivedCategory.singleFunctor _ 0).obj F) ≫
        (derivedDirectImage k).map (cupPullbackAugmentation h F)) ≫
    ((smallModuleDirectImage k).homologyRightDerivedFunctorObjSingleFunctorIso _ q).hom
end Square

section SectionsPullback
variable {A B : Type u} [CommRing A] [CommRing B] {Y Y' : Over S}
  (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B)) (g : Y' ⟶ Y)
  {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y) (h : X' ⟶ X)
  (k : X' ⟶ schemeSpace Y')

/-- Native derived restriction of scalars, an exact functor.
Source: Stacks 0E4S (blueprint: def-sfb-space-affine-cup-maps). -/
abbrev cupDerivedRestriction :=
  (ModuleCat.restrictScalars (spaceAffineRingMap e e' g)).mapDerivedCategory

/-- The ordinary and derived sections compositors between two affine scalar bases.
Source: Stacks 03G8, 0E4S (blueprint: def-sfb-space-affine-cup-maps). -/
structure CupSectionsComparison where
  ordinary : smallModuleDirectImage h ⋙ affineScalarSections A Y e X f ≅
    affineScalarSections B Y' e' X' k ⋙ ModuleCat.restrictScalars (spaceAffineRingMap e e' g)
  derived : derivedDirectImage h ⋙ affineDerivedSections A Y e X f ≅
    affineDerivedSections B Y' e' X' k ⋙ cupDerivedRestriction e e' g

/-- Ordinary comparison is fixed on every chart, and derived comparison by the
ordinary comparison and the actual derived units on every K-injective complex.
Source: Stacks 03G8, 0D6E (blueprint: def-sfb-space-affine-cup-maps). -/
def CupSectionsComparisonSpec (d : CupSectionsComparison e e' g f h k) : Prop :=
  (∀ (M : X'.SmallModules)
    (s : (affineScalarSections A Y e X f).obj ((smallModuleDirectImage h).obj M))
    (V : X.EtaleSite) (q : ModuleChart h V) (b : X.structureSheaf.obj.obj (op V)),
    ((moduleDirectImageModel h).projection (X'.smallModuleEquivalence.inverse.obj M) V).app
      (op q)
      (((X.smallModuleEquivalence.unitIso.inv.app _).val.app (op V))
        ((fullModuleSection X _ s).val.app (op V) b)) =
    (fullModuleSection X' M (d.ordinary.hom.app M s)).val.app (op q.left)
      (moduleChartScalar h V q b)) ∧
  (∀ (I : CochainComplex X'.SmallModules ℤ) [I.IsKInjective],
    affineSectionsComplexUnit A Y e X f
        (((smallModuleDirectImage h).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (affineDerivedSections A Y e X f).map
        (spaceRightDerivedComplexUnit (smallModuleDirectImage h) I) ≫
      d.derived.hom.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso d.ordinary (.up ℤ)).hom.app I) ≫
      (ModuleCat.restrictScalars (spaceAffineRingMap e e' g)).mapDerivedCategoryFactors.inv.app
        (((affineScalarSections B Y' e' X' k).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (cupDerivedRestriction e e' g).map (affineSectionsComplexUnit B Y' e' X' k I))

/-- Existence and uniqueness of normalized sections compositors.
Source: Stacks 03G8, 0D6E, 0E4S (blueprint: def-sfb-space-affine-cup-maps).
Proof: flatten the compatible chart limits for direct image. The commuting square
identifies the A-actions, and the displayed chart equation determines both inverse
maps. Injective module sheaves are flasque, and their direct images are
global-section acyclic. The standard unbounded derived-sections composition
comparison follows by K-injective resolution and the flasque acyclic models.
Exact scalar restriction commutes with homology. On K-injective representatives
the displayed unit equation defines the derived comparison. Universal right
derivation proves existence, naturality and uniqueness. The ordinary inverse and resolution
comparison supply its inverse. -/
theorem cupSectionsComparison_existsUnique
    (w : h ≫ f = k ≫ (ObjectProperty.homMk
      ((Scheme.fppfTopology.over S).yoneda.map g) : schemeSpace Y' ⟶ schemeSpace Y)) :
    ∃! d, CupSectionsComparisonSpec e e' g f h k d := by
  sorry

/-- The unique chart- and unit-normalized compositors.
Source: Stacks 03G8, 0D6E (blueprint: def-sfb-space-affine-cup-maps). -/
def cupSectionsComparison
    (w : h ≫ f = k ≫ (ObjectProperty.homMk
      ((Scheme.fppfTopology.over S).yoneda.map g) : schemeSpace Y' ⟶ schemeSpace Y)) :=
  (cupSectionsComparison_existsUnique e e' g f h k w).choose

variable (w : h ≫ f = k ≫ (ObjectProperty.homMk
  ((Scheme.fppfTopology.over S).yoneda.map g) : schemeSpace Y' ⟶ schemeSpace Y))

/-- Ordinary pullback of sections: the adjunction unit followed by the canonical
sections/direct-image compositor.
Source: Stacks 03G8, 0H9A (blueprint: def-sfb-space-affine-cup-maps). -/
def affineCupSectionPullback (F : X.SmallModules) :
    (affineScalarSections A Y e X f).obj F ⟶
      (ModuleCat.restrictScalars (spaceAffineRingMap e e' g)).obj
        ((affineScalarSections B Y' e' X' k).obj ((smallModuleTensorPullback h).obj F)) :=
  (affineScalarSections A Y e X f).map ((spaceSmallTensorAdjunction h).unit.app F) ≫
    (cupSectionsComparison e e' g f h k w).ordinary.hom.app _

/-- Global derived pullback, with the canonical augmentation to ordinary coefficients.
Source: Stacks 07A7, 0H9A (blueprint: def-sfb-space-affine-cup-maps). -/
def affineCupDerivedPullback (F : X.SmallModules) :
    (affineDerivedSections A Y e X f).obj ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
      (cupDerivedRestriction e e' g).obj
        ((affineDerivedSections B Y' e' X' k).obj
          ((DerivedCategory.singleFunctor _ 0).obj ((smallModuleTensorPullback h).obj F))) :=
  (affineDerivedSections A Y e X f).map
      ((spaceDerivedAdjunction h).unit.app ((DerivedCategory.singleFunctor _ 0).obj F)) ≫
    (cupSectionsComparison e e' g f h k w).derived.hom.app _ ≫
    (cupDerivedRestriction e e' g).map
      ((affineDerivedSections B Y' e' X' k).map (cupPullbackAugmentation h F))

/-- Global cohomology pullback in the classical right-derived convention.
Source: Stacks 07A7, 0H9A (blueprint: def-sfb-space-affine-cup-maps). -/
def affineCupCohomologyPullback (F : X.SmallModules) (q : ℕ) :
    (affineCupH A Y e X f q).obj F ⟶
      (ModuleCat.restrictScalars (spaceAffineRingMap e e' g)).obj
        ((affineCupH B Y' e' X' k q).obj ((smallModuleTensorPullback h).obj F)) :=
  ((affineScalarSections A Y e X f).homologyRightDerivedFunctorObjSingleFunctorIso F q).inv ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).map
      (affineCupDerivedPullback e e' g f h k w F) ≫
    (Functor.mapDerivedCategoryHomologyFunctorIso
      (ModuleCat.restrictScalars (spaceAffineRingMap e e' g)) q).inv.app _ ≫
    (ModuleCat.restrictScalars (spaceAffineRingMap e e' g)).map
      ((affineScalarSections B Y' e' X' k).homologyRightDerivedFunctorObjSingleFunctorIso
        ((smallModuleTensorPullback h).obj F) q).hom
end SectionsPullback

end AlgebraicGeometry.AlgebraicSpace
