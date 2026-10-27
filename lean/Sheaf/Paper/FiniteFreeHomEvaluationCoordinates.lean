module

public import Sheaf.Paper.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit

/-! # Canonical finite-free derived Hom evaluation coordinates

Source: thm-coef-finite-hom, proof paragraphs 2–3, finite-free evaluation calculation
(blueprint: def-sf-finite-free-hom-evaluation-coordinates).
All data is constructed from the published closed structure, standard basis and scalar unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The existing small-hom category instance, shared by all coordinate maps.
Source: etale derived size convention
(blueprint: def-sf-finite-free-hom-evaluation-coordinates). -/
abbrev lisseHomModuleDerivedCategory
    (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    Category.{u + 1} (Etale.DerivedCategoryModule R T) := inferInstance

attribute [local instance] lisseHomModuleDerivedCategory

/-- Evaluation at each supplied vector of a finite basis, followed by the product map.
Source: finite-free Hom calculation (blueprint: def-sf-finite-free-hom-evaluation-coordinates).
For t=0 the target is the empty product; in the etale derived category this is zero. -/
def lisseHomEvaluationCoordinates {C : Type v} [Category.{w} C]
    [MonoidalCategory C] [MonoidalClosed C]
    (t : ℕ) [HasProductsOfShape (Fin t) C] {K : C}
    (basis : Fin t → (𝟙_ C ⟶ K)) (N : C) :
    (ihom K).obj N ⟶ ∏ᶜ (fun _ : Fin t ↦ N) :=
  Pi.lift (fun i ↦ (λ_ ((ihom K).obj N)).inv ≫
    (basis i ▷ ((ihom K).obj N)) ≫ (ihom.ev K).app N)

/-- The standard constant-sheaf functor, sharing its canonical sheafification data.
Source: constant finite free modules (blueprint: def-sf-finite-free-hom-evaluation-coordinates). -/
abbrev lisseHomConstantFunctor (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    ModuleCat.{u + 1} R ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)

/-- The published tensor-unit isomorphism with shared constant-sheaf data.
Source: constant coefficient unit (blueprint: def-sf-finite-free-hom-evaluation-coordinates). -/
def lisseHomConstantUnitIso (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    𝟙_ (Etale.DerivedCategoryModule R T) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((lisseHomConstantFunctor R T).obj (ModuleCat.of R R)) :=
  Etale.unitIsoSingleFunctorConstantSheaf R T

/-- The standard basis vectors of the constant free sheaf, placed in degree zero.
Source: finite-free Hom calculation (blueprint: def-sf-finite-free-hom-evaluation-coordinates). -/
def lisseHomStandardBasis (R : Type (u + 1)) [CommRing R] (T : Scheme.{u})
    (t : ℕ) (i : Fin t) :
    (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((lisseHomConstantFunctor R T).obj
        (ModuleCat.of R R)) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((lisseHomConstantFunctor R T).obj
          (ModuleCat.of R (Fin t → R))) :=
  (_root_.DerivedCategory.singleFunctor _ 0).map
      ((lisseHomConstantFunctor R T).map
        (ModuleCat.ofHom (LinearMap.single R (fun _ : Fin t ↦ R) i)))

/-- Evaluation coordinates before coefficient specialization, retaining the same closed
structure as the published etale derived Hom.
Source: finite-free evaluation (blueprint: def-sf-finite-free-hom-evaluation-coordinates). -/
def lisseHomCoordinatesGeneral
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) (t : ℕ)
    (K N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A))
    (basis : Fin t → (𝟙_ (_root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) ⟶ K)) :
    ((Etale.derivedHom A T).obj (op K)).obj N ⟶ ∏ᶜ (fun _ : Fin t ↦ N) :=
  lisseHomEvaluationCoordinates t basis N

/-- Evaluation coordinates with the degree-zero constant coefficient sheaf as unit.
Source: finite-free evaluation (blueprint: def-sf-finite-free-hom-evaluation-coordinates). -/
def lisseHomCoordinatesRing (R : Type (u + 1)) [CommRing R] (T : Scheme.{u})
    (t : ℕ) (K N : Etale.DerivedCategoryModule R T)
    (basis : Fin t → ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((lisseHomConstantFunctor R T).obj
        (ModuleCat.of R R)) ⟶ K)) :
    ((Etale.derivedHom (ModuleCat.{u + 1} R) T).obj (op K)).obj N ⟶
      ∏ᶜ (fun _ : Fin t ↦ N) :=
  lisseHomCoordinatesGeneral (ModuleCat.{u + 1} R) T t K N
    (fun i ↦ (lisseHomConstantUnitIso R T).hom ≫ basis i)

/-- Transport supplied vectors through a trivialization of their common target.
Source: finite-free evaluation transport
(blueprint: def-sf-finite-free-hom-evaluation-coordinates). -/
def lisseHomTransportBasis {C : Type v} [Category.{w} C] {U V K : C}
    (t : ℕ) (basis : Fin t → (U ⟶ V)) (e : K ≅ V) (i : Fin t) : U ⟶ K :=
  basis i ≫ e.inv

/-- Standard vectors transported through a chosen degree-zero trivialization.
Source: finite-free evaluation transport
(blueprint: def-sf-finite-free-hom-evaluation-coordinates). -/
abbrev lisseHomTrivializedBasis (R : Type (u + 1)) [CommRing R] (T : Scheme.{u})
    (t : ℕ) (K : Etale.DerivedCategoryModule R T) :=
  lisseHomTransportBasis (K := K) t (lisseHomStandardBasis R T t)

end WeilConjectures
