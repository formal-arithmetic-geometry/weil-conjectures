module

public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.Paper.EtaleCtfChartDomain
import Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite-ring chart adjunctions

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-exceptional.proof.md`, Charts paragraph
(blueprint: lem-sp-chart-finite-ring-adjunction).

The affine space is the existing ordered affine-line tower, including its identity
stage. All restrictions below are full subcategories, with their ambient morphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 1000
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false

universe u v w
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
set_option backward.isDefEq.respectTransparency true
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.ChartFiniteRingNormalization
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

/-- Canonical shiftedComp comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev shiftedComp := @_root_.AlgebraicGeometry.Etale.shiftedComp

/-- Canonical tensorShiftCompGeneral comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev tensorShiftCompGeneral := @_root_.AlgebraicGeometry.Etale.tensorShiftCompGeneral

/-- Canonical comparison of the derived product of two degree-zero sheaves, with
flat first factor, to their ordinary tensor product followed by the fixed Tate product.
Source: Charts paragraph, the affine Tate normal form
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev singleProductGeneral := @_root_.AlgebraicGeometry.Etale.singleProductGeneral

/-- Canonical lineShiftGeneral comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev lineShiftGeneral := @_root_.AlgebraicGeometry.Etale.lineShiftGeneral

/-- Canonical singleE comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev singleE := @_root_.AlgebraicGeometry.Etale.singleE

/-- Canonical lineR comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev lineR := @_root_.AlgebraicGeometry.Etale.lineR

/-- Canonical singleEPullback comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev singleEPullback := @_root_.AlgebraicGeometry.Etale.singleEPullback

/-- Canonical tensorEPullback comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev tensorEPullback := @_root_.AlgebraicGeometry.Etale.tensorEPullback

/-- Canonical lineENormalForm comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev lineENormalForm := @_root_.AlgebraicGeometry.Etale.lineENormalForm

/-- Degree-zero Tate multiplication in the derived category, with its flatness
witness and the normalized ordinary Tate product kept as separate inputs.
Source: Charts paragraph, the affine Tate normal form
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev productE := @_root_.AlgebraicGeometry.Etale.productE

/-- Canonical towerENormalForm comparison for the ordered chart normalization.
Source: Charts paragraph, coordinate tensor/pullback/shift comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
abbrev towerENormalForm := @_root_.AlgebraicGeometry.Etale.towerENormalForm

section General
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  (N : ℕ) (E : ∀ X : Scheme.{u}, ℕ → Sheaf X.smallEtaleTopology B)
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (upperStar B f).PreservesFlat]
  (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsUnit (N : Γ(Y, ⊤)) → ∀ d : ℕ,
    (upperStar B f).obj (E Y d) ≅ E X d)
  (e0 : ∀ X : Scheme.{u}, E X 0 ≅ (constantSheaf X.smallEtaleTopology B).obj (𝟙_ B))
  (flat : ∀ X : Scheme.{u}, IsUnit (N : Γ(X, ⊤)) → ∀ d, ObjectProperty.flat (E X d))
  (prod : ∀ X : Scheme.{u}, IsUnit (N : Γ(X, ⊤)) → ∀ d : ℕ,
    ((curriedTensor (Sheaf X.smallEtaleTopology B)).obj (E X d)).obj (E X 1) ≅ E X (d + 1))

/-- Canonical chart normalization, natural in the input complex.
Source: Charts paragraph, ordered tensor and inverse-image comparisons
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartENormalForm {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) :
    (affineTraceRightTower (fun i ↦ lineR B E (affineTraceTower Y i)) d ⋙
      (upperStar B e).leftDerivedFunctor) ≅
      (upperStar B (e ≫ affineTraceProjection Y d)).leftDerivedFunctor ⋙
        derivedTensorRight B U (singleE B E U d) ⋙ shiftFunctor _ (2 * (d : ℤ)) :=
  Functor.isoWhiskerRight (towerENormalForm B N E c e0 flat prod Y hY d) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (tensorEPullback B N E c e (affineTraceInvertible N Y hY d) d (2 * (d : ℤ))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarComp B e (affineTraceProjection Y d)).symm _

end General
end AlgebraicGeometry.Etale.ChartFiniteRingNormalization

namespace AlgebraicGeometry.ProEtale.ChartFiniteRing
open AdjunctionTransfer MonoidalCategory

/-- The ordered left tower compared with any chosen affine compactification, on D+.
Every factor is the existing coordinate composition or common-refinement comparison.
Source: Charts paragraph, ordered affine-space left comparison
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
def affineLeftOnPlus (R : Type (u + 1)) [CommRing R] [Finite R]
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    (c : Compactification (affineTraceProjection Y d)) :
    _root_.DerivedCategory.Plus.ι ⋙ Etale.affineTraceLeft R Y d ≅
      _root_.DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c :=
  (Etale.affineTracePlusCompatibility R Y d).symm ≪≫
    Functor.isoWhiskerRight (Etale.affineTraceCompactSupportComparison R Y d)
      _root_.DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusIso R
        (HasCompactification.compactification (affineTraceProjection Y d)) c)
      _root_.DerivedCategory.Plus.ι ≪≫
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility (ModuleCat.{u + 1} R) c

/-- The specified graph-normalized comparison from sum-then-affine integration to
compact support, with its bounded-below endpoints explicit.
Source: Charts paragraph, graph normalization and chosen common refinement
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
def chartLeftOnPlus (R : Type (u + 1)) [CommRing R] [Finite R]
    (M : Etale.EtaleCompactSupportNormalization R)
    {U Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian Y]
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e]
    (cp : Compactification (affineTraceProjection Y d))
    (cg : Compactification (e ≫ affineTraceProjection Y d)) :
    _root_.DerivedCategory.Plus.ι ⋙
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategory ⋙
          Etale.affineTraceLeft R Y d ≅
      _root_.DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg :=
  have := affineTraceNoetherian Y d
  Functor.isoWhiskerRight
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} R) e
        inferInstance).mapDerivedCategoryPlusCompatibility.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategoryPlus
      (affineLeftOnPlus R Y d cp) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} R) e
        inferInstance).mapDerivedCategoryPlusCompatibility _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Etale.etaleAmbientLeftComparison R M e (affineTraceProjection Y d) cp cg)

/-- The full-subcategory restriction of the existing ordered geometric chart right
functor. The membership witness changes neither objects nor arrows.
Source: Charts paragraph, H et = e* p* (d)[2d]
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
def etaleRight (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y : Scheme.{u}} (N : ℕ) (hR : (N : R) = 0)
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    (h : ∀ K, etaleProperty R Y K → etaleProperty R U
      ((Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e).obj K)) :
    (etaleProperty R Y).FullSubcategory ⥤ (etaleProperty R U).FullSubcategory :=
  (etaleProperty R U).lift ((etaleProperty R Y).ι ⋙
    Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e)
    (fun K ↦ h K.obj K.property)

/-- The geometric pro-etale chart functor with the actual comparison image of the
finite Tate twist. This is a concrete pullback, tensor product and shift.
Source: Charts paragraph, H pro = e* p* (d)[2d]
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
def geometricRight (R : Type (u + 1)) [CommRing R]
    {U Y : Scheme.{u}} (N : ℕ) (hR : (N : R) = 0)
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) :=
  (upperStar (ModuleCat.{u + 1} R) (e ≫ affineTraceProjection Y d)).mapDerivedCategory ⋙
    (derivedTensor (ModuleCat.{u + 1} R) U).flip.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} R) U).obj
          (Scheme.finiteEtaleTateSheaf R N U hR (d : ℤ)))) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- The canonical coordinate-tower normalization, retaining the actual tensor, shift,
pullback and Tate-product maps that the existence theorem forgets.
Source: Charts paragraph, geometric identification; affine normal-form induction
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def affineRightNormalIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :=
  let t := Scheme.finiteEtaleTwistPullbackData R N hN hR
  let E := fun (T : Scheme.{u}) (d : ℕ) ↦ Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)
  let c := fun {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) ↦
    t.c f hY (affineTracePullbackInvertible N f hY) d
  let prod (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
      ((curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))).obj (E T d)).obj
        (E T 1) ≅ E T (d + 1) :=
    t.p T hT d 1 ≪≫ eqToIso
      (congrArg (Scheme.finiteEtaleTateSheaf R N T hR) (by omega))
  (Etale.ChartFiniteRingNormalization.towerENormalForm (ModuleCat.{u + 1} R)
    N E c (fun T ↦ Iso.refl (E T 0)) flat prod Y hY d)


/-- The canonical coordinate-tower normalization, retaining the actual tensor, shift,
pullback and Tate-product maps that the existence theorem forgets.
Source: Charts paragraph, geometric identification; affine normal-form induction
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def affineRightNormalComponent (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    (Y : Scheme.{u}) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ)
    (K : Etale.DerivedCategoryModule R Y) :=
  (affineRightNormalIso R N hN hR flat Y hY d).app K

/-- The canonical ordinary chart normalization, pulling the Tate power through e*.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def etaleChartNormalIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) :
    Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e ≅
      Etale.ordinaryFinitePullback R (e ≫ affineTraceProjection Y d) ⋙
        Etale.derivedTensorRight (ModuleCat.{u + 1} R) U
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateSheaf R N U hR (d : ℤ))) ⋙
        shiftFunctor _ (2 * (d : ℤ)) :=
  let t := Scheme.finiteEtaleTwistPullbackData R N hN hR
  let E := fun (T : Scheme.{u}) (d : ℕ) ↦ Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)
  let c := fun {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) ↦
    t.c f hY (affineTracePullbackInvertible N f hY) d
  let prod (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
      ((curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))).obj (E T d)).obj
        (E T 1) ≅ E T (d + 1) :=
    t.p T hT d 1 ≪≫ eqToIso
      (congrArg (Scheme.finiteEtaleTateSheaf R N T hR) (by omega))
  Etale.ChartFiniteRingNormalization.chartENormalForm (ModuleCat.{u + 1} R)
    N E c (fun T ↦ Iso.refl (E T 0)) flat prod hY d e

/-- The canonical ordinary chart normalization, pulling the Tate power through e*.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def etaleChartNormalComponent (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    (K : Etale.DerivedCategoryModule R Y) :=
  (etaleChartNormalIso R N hN hR flat hY d e).app K

/-- Flip a tensor comparison with its coefficient categories fixed.
Source: functor naturality (blueprint: lem-sp-chart-finite-ring-adjunction). -/
def flipTensorComparison {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (F : C ⥤ D)
    (h : (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S) (L : C) :
    T.flip.obj L ⋙ F ≅ F ⋙ S.flip.obj (F.obj L) :=
  NatIso.ofComponents (fun K ↦ (h.app K).app L)
    (fun f ↦ congr_app (h.hom.naturality f) L)

/-- The canonical monoidal comparison with a fixed right tensor factor.
Source: Charts paragraph, the monoidal site comparison
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartTensorComparison
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (U : Scheme.{u}) [(comparisonUpperStar B U).PreservesFlat]
    (L : _root_.DerivedCategory (Sheaf U.smallEtaleTopology B)) :
    Etale.derivedTensorRight B U L ⋙ (comparisonUpperStar B U).mapDerivedCategory ≅
      (comparisonUpperStar B U).mapDerivedCategory ⋙
        (derivedTensor B U).flip.obj ((comparisonUpperStar B U).mapDerivedCategory.obj L) :=
  let C := comparisonUpperStar B U
  let j := flipTensorComparison (Etale.derivedTensor B U) (derivedTensor B U)
    C.leftDerivedFunctor (asIso C.leftDerivedTensorComparison) L
  Functor.isoWhiskerLeft _ C.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    j ≪≫ Functor.isoWhiskerRight C.leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.isoWhiskerLeft C.mapDerivedCategory
      ((derivedTensor B U).flip.mapIso (C.leftDerivedFunctorIsoMapDerivedCategory.app L))


/-- Canonical site, tensor and shift comparison with a generic coefficient category.
The coefficient category stays explicit to avoid expanding the module tensor construction.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartGeometryComparison
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {U Y : Scheme.{u}} (f : U ⟶ Y) [(Etale.upperStar B f).PreservesFlat]
    [(comparisonUpperStar B U).PreservesFlat]
    (L : Sheaf U.smallEtaleTopology B) (b : ℤ) :
    ((Etale.upperStar B f).leftDerivedFunctor ⋙
        Etale.derivedTensorRight B U ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ⋙
        shiftFunctor _ b) ⋙ (comparisonUpperStar B U).mapDerivedCategory ≅
      (comparisonUpperStar B Y).mapDerivedCategory ⋙
        (upperStar B f).mapDerivedCategory ⋙
          (derivedTensor B U).flip.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((comparisonUpperStar B U).obj L)) ⋙ shiftFunctor _ b :=
  let C := (comparisonUpperStar B U).mapDerivedCategory
  let square :
      (comparisonUpperStar B Y).mapDerivedCategory ⋙ (upperStar B f).mapDerivedCategory ≅
        (Etale.upperStar B f).mapDerivedCategory ⋙ C :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (comparisonUpperStarCompUpperStarIso B f) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  let pb := Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory B f) C ≪≫ square.symm
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (C.commShiftIso b) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (chartTensorComparison B U ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) _ ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight pb _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight ((derivedTensor B U).flip.mapIso
        (((comparisonUpperStar B U).mapDerivedCategorySingleFunctor 0).app L)) _))


/-- Compose a chart normal form with the canonical comparison of sites.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartGeometryWithNormalForm
    (B : Type v) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    {U Y : Scheme.{u}} (f : U ⟶ Y) [(Etale.upperStar B f).PreservesFlat]
    [(comparisonUpperStar B U).PreservesFlat]
    (L : Sheaf U.smallEtaleTopology B) (b : ℤ)
    (H : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B) ⥤
      _root_.DerivedCategory (Sheaf U.smallEtaleTopology B))
    (j : H ≅ (Etale.upperStar B f).leftDerivedFunctor ⋙
      Etale.derivedTensorRight B U ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ⋙
        shiftFunctor _ b) :=
  Functor.isoWhiskerRight j (comparisonUpperStar B U).mapDerivedCategory ≪≫
    chartGeometryComparison B f L b

/-- The canonical chart comparison as a natural isomorphism.
Source: Charts paragraph, coordinate normalization and site comparison
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartGeometryIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) :
    (Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory ⋙
        geometricRight R N hR d e :=
  chartGeometryWithNormalForm (ModuleCat.{u + 1} R) (e ≫ affineTraceProjection Y d)
    (Scheme.finiteEtaleTateSheaf R N U hR (d : ℤ)) (2 * (d : ℤ)) _
    (etaleChartNormalIso R N hN hR flat hY d e)

/-- The fixed comparison component from the ordinary ordered chart functor to the
geometric pro-etale functor: normal form, shift, monoidality, degree-zero Tate
comparison, and the canonical site/pullback interchange. No isomorphism is chosen.
Source: Charts paragraph, geometric identification
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
@[irreducible]
def chartGeometryComponent (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (flat : ∀ (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)))
    {U Y : Scheme.{u}} (hY : IsUnit (N : Γ(Y, ⊤)))
    (d : ℕ) (e : U ⟶ affineTraceTower Y d) (K : Etale.DerivedCategoryModule R Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.obj
        ((Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e).obj K) ≅
      (geometricRight R N hR d e).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.obj K) :=
  (chartGeometryIso R N hN hR flat hY d e).app K

/-- The full-subcategory restriction of the concrete geometric pro-etale right functor.
Source: Charts paragraph, H pro on the finite-Tor domain
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
def geometricRestriction (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y : Scheme.{u}} (N : ℕ) (hR : (N : R) = 0)
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    (h : ∀ K, proEtaleProperty R Y K →
      proEtaleProperty R U ((geometricRight R N hR d e).obj K)) :
    (proEtaleProperty R Y).FullSubcategory ⥤ (proEtaleProperty R U).FullSubcategory :=
  (proEtaleProperty R U).lift ((proEtaleProperty R Y).ι ⋙ geometricRight R N hR d e)
    (fun K ↦ h K.obj K.property)

/-- All the chart assertions for one of the two finite coefficient rings. The right
adjunction is first retained in its specified comparison/quasi-inverse coordinates;
its geometric identification and Brown identification are natural isomorphisms.
Source: Charts paragraph and the seven DAG proof steps
(blueprint: lem-sp-chart-finite-ring-adjunction). -/
structure Datum (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian Y]
    (N : ℕ) (hR : (N : R) = 0) (d : ℕ)
    (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (cp : Compactification (affineTraceProjection Y d))
    (cg : Compactification (e ≫ affineTraceProjection Y d))
    (M : Etale.EtaleCompactSupportNormalization R)
    (t : Etale.OrdinaryFiniteTwistTransport R N hR)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum R N hR t T hT)
    (hY : IsUnit (N : Γ(Y, ⊤))) where
  /-- The common torsion exponent is positive, including the zero-ring case N = 1. -/
  positive : 0 < N
  /-- Finite Tate powers are flat; only this proposition enters the canonical map. -/
  flatTwist (T : Scheme.{u}) (_hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ))
  /-- The pro-etale category has intrinsic constructible cohomology and the full Tor test. -/
  intrinsic (T : Scheme.{u}) [IsNoetherian T] :
    proEtaleProperty R T = fun K ↦
      _root_.DerivedCategory.TStructure.t.bounded K ∧
        (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T R
          ((_root_.DerivedCategory.homologyFunctor _ i).obj K)) ∧
        ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) T a b K
  /-- Etale compact support preserves the finite-Tor domain. -/
  hEt : ∀ K, etaleProperty R U K → etaleProperty R Y
    ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).obj K)
  /-- The geometric etale right functor preserves the finite-Tor domain. -/
  hRight : ∀ K, etaleProperty R Y K → etaleProperty R U
    ((Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e).obj K)
  /-- Pro-etale compact support preserves the finite-Tor domain. -/
  hPro : ∀ K, proEtaleProperty R U K → proEtaleProperty R Y
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).obj K)
  /-- The comparison inverse image preserves the domain on U. -/
  hU : ∀ K, etaleProperty R U K → proEtaleProperty R U
    ((comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.obj K)
  /-- The comparison inverse image preserves the domain on Y. -/
  hV : ∀ K, etaleProperty R Y K → proEtaleProperty R Y
    ((comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.obj K)
  /-- Comparison, with its quasi-inverse and endpoint isomorphisms, on U. -/
  eU : (etaleProperty R U).FullSubcategory ≌ (proEtaleProperty R U).FullSubcategory
  /-- Comparison, with its quasi-inverse and endpoint isomorphisms, on Y. -/
  eY : (etaleProperty R Y).FullSubcategory ≌ (proEtaleProperty R Y).FullSubcategory
  /-- The equivalence uses the specified comparison functor. -/
  heU : eU.functor = comparison R U hU
  /-- The equivalence uses the specified comparison functor. -/
  heY : eY.functor = comparison R Y hV
  /-- The etale chart adjunction on the full categories. -/
  adjEt : etaleLowerShriek R cg hEt ⊣ etaleRight R N hR d e hRight
  /-- Its counit is literally sum evaluation, then ordered affine integration,
  precomposed with the inverse graph-normalized left comparison. -/
  etaleCounit (K : (etaleProperty R Y).FullSubcategory) :
    (adjEt.counit.app K).hom =
      (chartLeftOnPlus R M d e cp cg).inv.app
          ((etaleToPlus R U).obj ((etaleRight R N hR d e hRight).obj K)) ≫
        (((Etale.derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} R) e inferInstance).ofNatIsoRight
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} R) e).symm).comp
          (Etale.affineTraceAdjunction R N hR t D Y hY d)).counit.app K.obj
  /-- The compact-support comparison on the full categories. -/
  cf : etaleLowerShriek R cg hEt ⋙ eY.functor ≅ eU.functor ⋙ proEtaleLowerShriek R cg hPro
  /-- Its inverse is exactly the fixed proper-counit/open comparison, not a free iso. -/
  fixedComparison (K : (etaleProperty R U).FullSubcategory) :
    (cf.inv.app K).hom =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).map
          (eqToHom (congrArg (fun F ↦ (F.obj K).obj) heU)) ≫
        (fixedCompactSupportComparisonIso R cg).hom.app ((etaleToPlus R U).obj K) ≫
        eqToHom (congrArg (fun F ↦ (F.obj ((etaleLowerShriek R cg hEt).obj K)).obj)
          heY).symm
  /-- The transported adjunction retains the chosen quasi-inverse. -/
  adjPro : proEtaleLowerShriek R cg hPro ⊣
    (eY.inverse ⋙ etaleRight R N hR d e hRight ⋙ eU.functor)
  /-- The actual transported counit, with the quasi-inverse endpoint map displayed. -/
  proCounit (K : (etaleProperty R Y).FullSubcategory) :
    adjPro.counit.app (eY.functor.obj K) =
      (proEtaleLowerShriek R cg hPro).map
          (eU.functor.map ((etaleRight R N hR d e hRight).map (eY.unitIso.inv.app K))) ≫
        cf.inv.app ((etaleRight R N hR d e hRight).obj K) ≫
        eY.functor.map (adjEt.counit.app K)
  /-- The concrete geometric functor preserves the full finite-Tor domain. -/
  hGeometry : ∀ K, proEtaleProperty R Y K →
    proEtaleProperty R U ((geometricRight R N hR d e).obj K)
  /-- The geometric identification is retained as data, with the following canonical equation. -/
  geometric : (eY.inverse ⋙ etaleRight R N hR d e hRight ⋙ eU.functor) ≅
    geometricRestriction R N hR d e hGeometry
  /-- Each component is the canonical coordinate normalization and site comparison,
  followed by the actual equivalence counit on Y. This excludes a sign twist. -/
  geometric_normalization (K : (proEtaleProperty R Y).FullSubcategory) :
    (geometric.hom.app K).hom =
      eqToHom (congrArg (fun F ↦
        (F.obj ((etaleRight R N hR d e hRight).obj (eY.inverse.obj K))).obj) heU) ≫
      (chartGeometryComponent R N positive hR flatTwist hY d e
        (eY.inverse.obj K).obj).hom ≫
      (geometricRight R N hR d e).map
        (eqToHom (congrArg (fun F ↦ (F.obj (eY.inverse.obj K)).obj) heY.symm) ≫
          (eY.counitIso.hom.app K).hom)
  /-- Every given Brown adjunction on the same localizing closures restricts, and its
  right adjoint has exactly one counit-preserving identification with this functor. -/
  brown
      (hLoc : ∀ K, CategoryTheory.localizingClosure (proEtaleProperty R U) K →
        CategoryTheory.localizingClosure (proEtaleProperty R Y)
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).obj K))
      (J : (CategoryTheory.localizingClosure (proEtaleProperty R Y)).FullSubcategory ⥤
        (CategoryTheory.localizingClosure (proEtaleProperty R U)).FullSubcategory)
      (adjBrown : localizingLowerShriek R cg hLoc ⊣ J) :
    ∃ hJ : ∀ K : (proEtaleProperty R Y).FullSubcategory,
        proEtaleProperty R U ((J.obj ((toLocalizing R Y).obj K)).obj),
      ∃! θ : geometricRestriction R N hR d e hGeometry ≅
          brownRestriction R J hJ,
        ∀ K : (proEtaleProperty R Y).FullSubcategory,
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).map
              ((θ.hom.app K).hom) ≫
            (adjBrown.counit.app ((toLocalizing R Y).obj K)).hom =
              (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).map
                ((geometric.inv.app K).hom) ≫ (adjPro.counit.app K).hom

private local instance etaleBoundedIso (R : Type (u + 1)) [CommRing R] [Finite R]
    (T : Scheme.{u}) :
    (Etale.DerivedCategory.isBoundedConstructible R T).IsClosedUnderIsomorphisms where
  of_iso e h := by
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      ?_, ?_⟩
    · have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (h.1 q)
      exact Scheme.IsConstructibleSheaf.of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e)
    · obtain ⟨a, b, hab, hz⟩ := h.2
      exact ⟨a, b, hab, fun q hq ↦ (hz q hq).of_iso
        ((_root_.DerivedCategory.homologyFunctor _ q).mapIso e).symm⟩

private theorem chartTwist_flat (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    ObjectProperty.flat (Scheme.finiteEtaleTateSheaf R N T hR (d : ℤ)) := by
  apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
  apply (Scheme.finite_etale_torsion_twist_line T N hN _ R hR d).2.2.1
  intro x
  simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom

private theorem chartIntrinsic (R : Type (u + 1)) [CommRing R] [Finite R]
    (T : Scheme.{u}) [IsNoetherian T] :
    proEtaleProperty R T = fun K ↦
      _root_.DerivedCategory.TStructure.t.bounded K ∧
        (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T R
          ((_root_.DerivedCategory.homologyFunctor _ i).obj K)) ∧
        ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} R) T a b K := by
  funext K
  apply propext
  have hc := congrFun (exceptionalTransport_constructible_comparison R T) K
  change (_ ∧ _root_.DerivedCategory.finiteTorAmplitude _ K) ↔ _
  rw [← hc]
  constructor
  · rintro ⟨⟨hb, hcs⟩, a, b, ht⟩
    exact ⟨hb, hcs, min a b, b, min_le_right _ _,
      ht.mono (min_le_left _ _) le_rfl⟩
  · rintro ⟨hb, hcs, a, b, _, ht⟩
    exact ⟨⟨hb, hcs⟩, a, b, ht⟩

private theorem existsChartDatum
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian Y]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (d : ℕ)
    (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (cp : Compactification (affineTraceProjection Y d))
    (cg : Compactification (e ≫ affineTraceProjection Y d))
    (M : Etale.EtaleCompactSupportNormalization R)
    (t : Etale.OrdinaryFiniteTwistTransport R N hR)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum R N hR t T hT)
    (hY : IsUnit (N : Γ(Y, ⊤)))
    (hEt : ∀ K, etaleProperty R U K → etaleProperty R Y
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).obj K))
    (hU : ∀ K, etaleProperty R U K → proEtaleProperty R U
      ((comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.obj K))
    (hV : ∀ K, etaleProperty R Y K → proEtaleProperty R Y
      ((comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.obj K))
    [(comparison R U hU).IsEquivalence] [(comparison R Y hV).IsEquivalence]
    (hOp : ∀ K, etaleProperty R Y K → etaleProperty R U
      ((etaleChartOperation R N hR (e ≫ affineTraceProjection Y d) d
        (2 * (d : ℤ))).obj K)) :
    Nonempty (Datum R N hR d e cp cg M t D hY) := by
  classical
  let flat := chartTwist_flat R N hN hR
  let eU := (comparison R U hU).asEquivalence
  let eY := (comparison R Y hV).asEquivalence
  have hRight : ∀ K, etaleProperty R Y K → etaleProperty R U
      ((Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e).obj K) := by
    intro K hK
    let f := e ≫ affineTraceProjection Y d
    let L := (_root_.DerivedCategory.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateSheaf R N U hR (d : ℤ))
    let pb := (Etale.ordinaryFinitePullback R f).obj K
    let j : (Etale.derivedTensorRight (ModuleCat.{u + 1} R) U L ⋙
        shiftFunctor _ (2 * (d : ℤ))).obj pb ≅
        (etaleChartOperation R N hR f d (2 * (d : ℤ))).obj K :=
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        ((((Etale.derivedTensor (ModuleCat.{u + 1} R) U).flip.obj L).mapIso
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} R) f).app K)) ≪≫
          ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} R) U).app
            ((Etale.upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory.obj K)).app L)
    exact (etaleProperty R U).prop_of_iso
      (etaleChartNormalComponent R N hN hR flat hY d e K ≪≫ j).symm (hOp K hK)
  let S := (Etale.etaleLowerShriek (ModuleCat.{u + 1} R) e inferInstance).mapDerivedCategory
  let F := Etale.affineTraceLeft R Y d
  let H := Etale.affineTraceRight R N hR Y d ⋙ Etale.ordinaryFinitePullback R e
  let a : S ⋙ F ⊣ H :=
    ((Etale.derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) e inferInstance).ofNatIsoRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} R) e).symm).comp
      (Etale.affineTraceAdjunction R N hR t D Y hY d)
  let l : (etaleProperty R U).ι ⋙ (S ⋙ F) ≅
      etaleLowerShriek R cg hEt ⋙ (etaleProperty R Y).ι :=
    Functor.isoWhiskerLeft (etaleToPlus R U) (chartLeftOnPlus R M d e cp cg)
  let r : (etaleProperty R Y).ι ⋙ H ≅
      etaleRight R N hR d e hRight ⋙ (etaleProperty R U).ι := Iso.refl _
  let adjEt := a.restrictFullyFaithful (etaleProperty R U).fullyFaithfulι
    (etaleProperty R Y).fullyFaithfulι l r
  have hcounit (K : (etaleProperty R Y).FullSubcategory) :
      (adjEt.counit.app K).hom =
        (chartLeftOnPlus R M d e cp cg).inv.app
          ((etaleToPlus R U).obj ((etaleRight R N hR d e hRight).obj K)) ≫
            a.counit.app K.obj := by
    have hh := a.map_restrictFullyFaithful_counit_app
      (etaleProperty R U).fullyFaithfulι (etaleProperty R Y).fullyFaithfulι l r K
    change (adjEt.counit.app K).hom =
      l.inv.app ((etaleRight R N hR d e hRight).obj K) ≫
        (S ⋙ F).map (𝟙 _) ≫ a.counit.app K.obj at hh
    rw [(S ⋙ F).map_id] at hh
    erw [Category.id_comp] at hh
    exact hh
  have hPro : ∀ K, proEtaleProperty R U K → proEtaleProperty R Y
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).obj K) := by
    intro K hK
    let K' : (proEtaleProperty R U).FullSubcategory := ⟨K, hK⟩
    let L := (eU.inverse.obj K')
    let j := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).mapIso
        ((proEtaleProperty R U).ι.mapIso (eU.counitIso.app K')).symm ≪≫
      (fixedCompactSupportComparisonIso R cg).app ((etaleToPlus R U).obj L)
    exact (proEtaleProperty R Y).prop_of_iso j.symm (hV _ (hEt _ L.property))
  let cf : etaleLowerShriek R cg hEt ⋙ eY.functor ≅
      eU.functor ⋙ proEtaleLowerShriek R cg hPro :=
    NatIso.ofComponents (fun K ↦ (proEtaleProperty R Y).isoMk
      (((fixedCompactSupportComparisonIso R cg).app ((etaleToPlus R U).obj K)).symm))
      (by
        intro K L f
        apply ObjectProperty.hom_ext
        exact (fixedCompactSupportComparisonIso R cg).inv.naturality
          ((etaleToPlus R U).map f))
  obtain ⟨adjPro, hCounit, hBrown⟩ :=
    etaleProEtaleAdjunctionTransferOfComparison R cg hU hV eU eY rfl rfl
    hEt hPro cf (etaleRight R N hR d e hRight) adjEt
  have hGeometry : ∀ K, proEtaleProperty R Y K →
      proEtaleProperty R U ((geometricRight R N hR d e).obj K) := by
    intro K hK
    let K' : (proEtaleProperty R Y).FullSubcategory := ⟨K, hK⟩
    let L := eY.inverse.obj K'
    let j := chartGeometryComponent R N hN hR flat hY d e L.obj ≪≫
      (geometricRight R N hR d e).mapIso
        ((proEtaleProperty R Y).ι.mapIso (eY.counitIso.app K'))
    exact (proEtaleProperty R U).prop_of_iso j (hU _ (hRight _ L.property))
  let ambient :
      (eY.inverse ⋙ etaleRight R N hR d e hRight ⋙ eU.functor) ⋙
          (proEtaleProperty R U).ι ≅
        geometricRestriction R N hR d e hGeometry ⋙ (proEtaleProperty R U).ι :=
    Functor.isoWhiskerLeft (eY.inverse ⋙ (etaleProperty R Y).ι)
        (chartGeometryIso R N hN hR flat hY d e) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight eY.counitIso (proEtaleProperty R Y).ι)
        (geometricRight R N hR d e)
  let geometric : (eY.inverse ⋙ etaleRight R N hR d e hRight ⋙ eU.functor) ≅
      geometricRestriction R N hR d e hGeometry :=
    ((proEtaleProperty R U).fullyFaithfulι.whiskeringRight _).preimageIso ambient
  refine ⟨{
    positive := hN
    flatTwist := flat
    intrinsic := chartIntrinsic R
    hEt := hEt
    hRight := hRight
    hPro := hPro
    hU := hU
    hV := hV
    eU := eU
    eY := eY
    heU := rfl
    heY := rfl
    adjEt := adjEt
    etaleCounit := hcounit
    cf := cf
    fixedComparison := ?_
    adjPro := adjPro
    proCounit := hCounit
    hGeometry := hGeometry
    geometric := geometric
    geometric_normalization := ?_
    brown := ?_ }⟩
  · intro K
    set_option backward.isDefEq.respectTransparency false in
      simp only [eqToHom_refl,
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).map_id,
        Category.id_comp, Category.comp_id]
    rfl
  · intro K
    set_option backward.isDefEq.respectTransparency false in
      simp only [eqToHom_refl, Category.id_comp]
    change (ambient.hom.app K) = _
    unfold chartGeometryComponent
    rfl
  · intro hLoc J adjBrown
    obtain ⟨hJ, h⟩ := hBrown hLoc J adjBrown
    let ε : (eY.inverse ⋙ etaleRight R N hR d e hRight ⋙ eU.functor) ⋙
        proEtaleLowerShriek R cg hPro ⟶ 𝟭 _ := adjPro.counit
    let δ : brownRestriction R J hJ ⋙ proEtaleLowerShriek R cg hPro ⟶ 𝟭 _ :=
      { app := fun K ↦ ObjectProperty.homMk
          (adjBrown.counit.app ((toLocalizing R Y).obj K)).hom
        naturality := by
          intro K L f
          apply ObjectProperty.hom_ext
          exact congrArg (fun z ↦ z.hom)
            (adjBrown.counit.naturality ((toLocalizing R Y).map f)) }
    have h' : ∃! γ : (eY.inverse ⋙ etaleRight R N hR d e hRight ⋙ eU.functor) ≅
        brownRestriction R J hJ, ∀ K,
          (proEtaleLowerShriek R cg hPro).map (γ.hom.app K) ≫ δ.app K = ε.app K := by
      obtain ⟨γ, hγ, huniq⟩ := h
      refine ⟨γ, fun K ↦ (proEtaleProperty R Y).hom_ext (hγ K), ?_⟩
      intro θ hθ
      exact huniq θ (fun K ↦ congrArg (fun z ↦ z.hom) (hθ K))
    have hh := transportUniqueCounitIso (proEtaleLowerShriek R cg hPro) geometric ε δ h'
    refine ⟨hJ, ?_⟩
    obtain ⟨θ, hθ, huniq⟩ := hh
    refine ⟨θ, fun K ↦ congrArg (fun z ↦ z.hom) (hθ K), ?_⟩
    intro ψ hψ
    exact huniq ψ (fun K ↦ (proEtaleProperty R Y).hom_ext (hψ K))

/-- For both finite rings, the chart adjunction exists on the exact finite-Tor
categories, with the graph-normalized etale counit, the fixed site comparison,
the actual transported counit, the geometric right functor and the unique
counit-preserving Brown identification. No flatness of the coefficient map is assumed.
Source: blueprint main-20261015, sk-lem-sp-reduction-exceptional.proof.md,
Charts paragraph (blueprint: lem-sp-chart-finite-ring-adjunction).

Proof:
1. The standing schemes are Noetherian by finite type over the field
   (lem-weil-pbc-finite-type-over-noetherian); ell^n is invertible since ell differs
   from the positive characteristic. Finite coefficient rings are Noetherian.
   lem-sp-etale-ctf-chart-domain gives preservation by both etale chart functors.
   det-pe-finite-tor-comparison-noetherian preserves and reflects every Tor interval
   and gives the two comparison equivalences. The intrinsic constructibility
   comparison identifies their domains with bounded complexes having intrinsic
   constructible cohomology and finite pro-etale Tor amplitude.
2. Compose the exact sum adjunction of lem-amb-etale-adjoint-locality with the
   ordered affine adjunction of lem-amb-affine-space-top-trace, including its
   identity stage at d=0. The composite counit is affine integration following
   sum evaluation, by def-weil-pbc-composite-adjunction.
3. lem-sp-chart-left-scalar-normalization identifies the specified left comparison
   with graph normalization, coordinate composition and common refinement.
   Restrict the unchanged Hom bijections to the full finite-Tor subcategories.
   Its counit is the composite counit precomposed by chartLeftOnPlus inverse.
4. lem-sp-finite-compact-support-domains identifies the comparison with the fixed
   proper-counit/open isomorphism on bounded-below etale inputs. Essential
   surjectivity of comparison gives preservation by pro-etale compact support.
5. det-sp-et-proet-adjunction-transfer transports this precise adjunction through
   the two equivalences. Its Hom bijection ends by precomposition with cf inverse.
   Evaluate at the identity to obtain proCounit, including the quasi-inverse unit.
6. The canonical inverse-image, tensor and shift comparisons of
   lem-sp-etale-ctf-chart-domain identify the transported functor with geometricRight.
   The pro-etale Tate sheaf is exactly the comparison image of the etale one.
7. sk-prop-sf-rf-shriek-preservation restricts any given Brown adjunction on the
   localizing closures to these same full categories. det-sp-unique-right-adjoint
   transposes the two counits to mutually inverse natural transformations.
   Injectivity of the Brown Hom equivalence proves counit-preserving uniqueness.
   Apply this argument separately to A and B; the map between them needs no flatness.
-/
theorem chartFiniteRingAdjunction
    (ell pchar : ℕ) [Fact ell.Prime] (hp : 0 < pchar) (hne : ell ≠ pchar)
    (k : Type u) [Field k] [CharP k pchar]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_φ : A →+* B) (n : ℕ)
    (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    {U Y : Scheme.{u}} [U.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (_he : e ≫ affineTraceProjection Y d ≫ (Y ↘ Spec (.of k)) =
      (U ↘ Spec (.of k)))
    (cp : Compactification (affineTraceProjection Y d))
    (cg : Compactification (e ≫ affineTraceProjection Y d)) :
    ∃ (hU : IsNoetherian U) (hY : IsNoetherian Y)
      (hN : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤))),
      ∀ (MA : Etale.EtaleCompactSupportNormalization A)
        (tA : Etale.OrdinaryFiniteTwistTransport A (ell ^ n) hA)
        (DA : ∀ (T : Scheme.{u}) [IsNoetherian T]
          (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
          Etale.OrdinaryFiniteP1Datum A (ell ^ n) hA tA T hT)
        (MB : Etale.EtaleCompactSupportNormalization B)
        (tB : Etale.OrdinaryFiniteTwistTransport B (ell ^ n) hB)
        (DB : ∀ (T : Scheme.{u}) [IsNoetherian T]
          (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
          Etale.OrdinaryFiniteP1Datum B (ell ^ n) hB tB T hT),
        Nonempty (@Datum A _ _ U Y hU hY (ell ^ n) hA d e
          inferInstance inferInstance inferInstance inferInstance cp cg MA tA DA hN) ∧
        Nonempty (@Datum B _ _ U Y hU hY (ell ^ n) hB d e
          inferInstance inferInstance inferInstance inferInstance cp cg MB tB DB hN) := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian
    (U ↘ Spec (.of k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of k))
  have : IsNoetherian U := ⟨⟩
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := ⟨⟩
  have hN : 0 < ell ^ n := pow_pos (Fact.out : ell.Prime).pos _
  have hchar : ringChar k = pchar := ringChar.eq k pchar
  have : Fact (ringChar k).Prime :=
    ⟨hchar.symm ▸ (CharP.char_is_prime_or_zero k pchar).resolve_right (Nat.ne_of_gt hp)⟩
  have : Fact (ringChar k ≠ ell) := ⟨by simpa only [hchar] using hne.symm⟩
  have hunit : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)) := by
    have h : (ell : k) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime k
      (Fact.out : ell.Prime) hne.symm
    have hi := (isUnit_iff_ne_zero.mpr (pow_ne_zero n h)).map
      (Scheme.ΓSpecIso (.of k)).inv.hom
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hi.map (Y ↘ Spec (.of k)).appTop.hom
  refine ⟨inferInstance, inferInstance, hunit, ?_⟩
  intro MA tA DA MB tB DB
  have : (e ≫ affineTraceProjection Y d).IsOver (Spec (.of k)) := ⟨by simpa using _he⟩
  have singleRing (R : Type (u + 1)) [CommRing R] [Finite R]
      (hR : ((ell ^ n : ℕ) : R) = 0)
      (M : Etale.EtaleCompactSupportNormalization R)
      (t : Etale.OrdinaryFiniteTwistTransport R (ell ^ n) hR)
      (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
        (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
        Etale.OrdinaryFiniteP1Datum R (ell ^ n) hR t T hT) :
      Nonempty (Datum R (ell ^ n) hR d e cp cg M t D hunit) := by
    obtain ⟨hEt, ⟨hV, heV⟩, _, hOp, _⟩ := etaleCtfChartDomain ell k R n hR
      (e ≫ affineTraceProjection Y d) cg (e ≫ affineTraceProjection Y d)
    obtain ⟨_, ⟨hU, heU⟩, _⟩ := etaleCtfChartDomain ell k R n hR
      (e ≫ affineTraceProjection Y d) cg (𝟙 U)
    let _ := heU
    let _ := heV
    exact existsChartDatum R (ell ^ n) hN hR d e cp cg M t D hunit hEt hU hV
      (hOp d (2 * (d : ℤ)))
  exact ⟨singleRing A hA MA tA DA, singleRing B hB MB tB DB⟩

end AlgebraicGeometry.ProEtale.ChartFiniteRing
