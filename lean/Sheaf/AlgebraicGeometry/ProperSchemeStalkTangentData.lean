/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.ProperSchemeTangentData
public import Sheaf.AlgebraicGeometry.CompletedSchemeTangentData
public import Sheaf.AlgebraicGeometry.AffineSchemeDeformationComparison
public import Sheaf.AlgebraicGeometry.IsolatedCurveFormalLifting
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

/-! # Stalk and continuous completion compatibility of tangent classes

Source: Stacks Project, examples-defos.tex, Tags 0DYV and 0DZM; Cotangent Complex,
Tags 08SF and 08UW (blueprint: def-sfb-proper-scheme-stalk-tangent-data).
## Main definitions

- `localAlgebra`.
- `localAlgebra_isLocalRing`.
- `StalkComparison`.
- `StalkComparison.ext`.
- `IsStalkDeformation`.
- `ClosedCompletionCompatibility`.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open Algebra.CotangentResolution
namespace AlgebraicGeometry.ProperSchemeDeformation
variable [hRing : ∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
  [∀ X : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  {k : Type u} [Field k] {X : Scheme.{u}}

/-- Fix the recorded small-ring derived-category universe also for unbundled rings.
Source: Stacks 06UP (blueprint: def-sfb-proper-scheme-stalk-tangent-data). -/
local instance localDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := hRing (CommRingCat.of A)

/-- The local ring with the structural field map, using the existing scalar-to-stalk
construction. Source: Stacks 01HA (blueprint: def-sfb-proper-scheme-stalk-tangent-data). -/
def localAlgebra (f : X ⟶ Spec (.of k)) (x : X) : CommAlgCat.{u} k :=
  letI := (isolatedCurveScalarToStalk f x).toAlgebra
  CommAlgCat.of k (X.presheaf.stalk x)

/-- The local-algebra wrapper retains the scheme stalk's local-ring instance.
Source: Stacks 01HA (blueprint: def-sfb-proper-scheme-stalk-tangent-data). -/
instance localAlgebra_isLocalRing (f : X ⟶ Spec (.of k)) (x : X) :
    IsLocalRing (localAlgebra f x) :=
  inferInstanceAs (IsLocalRing (X.presheaf.stalk x))

/-- A stalk comparison fixed on every section of the standard polynomial model.
The unit comparison is fixed on ring germs. Source: Stacks 08SF and 08UW
(blueprint: def-sfb-proper-scheme-stalk-tangent-data). -/
structure StalkComparison (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    (f : X ⟶ Spec (.of k)) (x : X) where
  additive : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).Additive
  limits : PreservesFiniteLimits (RingedSpace.moduleStalkFunctor X.toRingedSpace x)
  colimits : PreservesFiniteColimits (RingedSpace.moduleStalkFunctor X.toRingedSpace x)
  square (V : X.Opens) (hx : x ∈ V) :
    TopCat.SheafCotangent.sectionArrow
      (Arrow.mk (Scheme.Modules.tensorPullbackRingMap f)) (op V) ⟶
        SchemeDeformation.affineArrow k (localAlgebra f x)
  left (V : X.Opens) (hx : x ∈ V) (a : k) :
    (square V hx).left (SchemeDeformation.inverseSection f ⊤ V (by simp)
      ((Scheme.ΓSpecIso (.of k)).inv a)) = a
  right (V : X.Opens) (hx : x ∈ V) (a : Γ(X, V)) :
    (square V hx).right a = X.presheaf.germ V x hx a
  map : ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
    (.up ℤ)).obj (SchemeDeformation.cotangentComplex C D f) ⟶
      standardComplex C (SchemeDeformation.affineArrow k (localAlgebra f x))
  comparison : DerivedCategory.Q.obj
    (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
      (.up ℤ)).obj (SchemeDeformation.cotangentComplex C D f)) ≅
        Algebra.CotangentResolution.cotangentComplex C
          (SchemeDeformation.affineArrow k (localAlgebra f x))
  normalization : comparison.hom = DerivedCategory.Q.map map
  sections (V : X.Opens) (hx : x ∈ V) (n : ℤ)
    (a : (standardComplex C (TopCat.SheafCotangent.sectionArrow
      (Arrow.mk (Scheme.Modules.tensorPullbackRingMap f)) (op V))).X n) :
    (map.f n) (TopCat.Presheaf.germ
      ((SchemeDeformation.cotangentComplex C D f).X n).val.presheaf V x hx
      (TopCat.SheafCotangent.sectionElement
        (D.sheaves X.carrier (Arrow.mk (Scheme.Modules.tensorPullbackRingMap f))).sections
        (op V) n a)) = (standardComplexMap C (square V hx)).f n a
  unit : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
    (SheafOfModules.unit X.ringCatSheaf) ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)
  unit_germs (V : X.Opens) (hx : x ∈ V) (a : Γ(X, V)) :
    unit.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
      V x hx a) = X.presheaf.germ V x hx a

/-- Localization on full cotangent Ext uses the exact stalk functor and the normalized
comparison above. Source: Stacks 08SF
(blueprint: def-sfb-proper-scheme-stalk-tangent-data). -/
def StalkComparison.ext {C : Coherence.{u}} {D : TopCat.SheafCotangent.Comparison C}
    {f : X ⟶ Spec (.of k)} {x : X} (s : StalkComparison C D f x)
    (ξ : TangentExt C D f) :=
  letI := s.additive
  letI := s.limits
  letI := s.colimits
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  s.comparison.inv ≫ S.mapDerivedCategoryFactors.inv.app _ ≫
    S.mapDerivedCategory.map ξ ≫ (S.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _ ≫
    (S.mapDerivedCategorySingleFunctor 0).hom.app _⟦(1 : ℤ)⟧' ≫
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).map
      s.unit.hom)⟦(1 : ℤ)⟧'

/-- A marked algebra deformation is the actual stalk of the scheme deformation.
Scalar and marking equations pin both identifications. Source: Stacks 0DZM
(blueprint: def-sfb-proper-scheme-stalk-tangent-data). -/
structure IsStalkDeformation (f : X ⟶ Spec (.of k)) (x : X)
    (Y : SchemeDeformation.Lift f
      (SchemeDeformation.directionReduction k (ModuleCat.of k k)))
    (Q : Algebra.FlatDeformation.Groupoid (localAlgebra f x)
      (ArtinDeformation.squareZeroTest (R := k) (k := k) k)) where
  coordinate : Algebra.FlatDeformation.algebra Q ≃+*
    Y.space.presheaf.stalk (Y.marking x)
  scalar (a : ArtinDeformation.ring
    (ArtinDeformation.squareZeroTest (R := k) (k := k) k)) :
    coordinate (Algebra.FlatDeformation.scalar Q a) =
      Y.space.presheaf.germ ⊤ (Y.marking x) (by trivial)
        (Y.projection.appTop ((Scheme.ΓSpecIso
          (dualDirectionRing k)).inv a))
  marking (a : Algebra.FlatDeformation.algebra Q) :
    Algebra.FlatDeformation.marking Q a = Y.marking.stalkMap x (coordinate a)

/-- Completion compatibility, tested at each closed point on every marked lift and
on every presentation Ext representative. Its lower horizontal arrow is exact scalar
extension of the conormal complex; its upper arrow is actual adic completion.
Source: Stacks 0DYV, 0DZM and 07NJ
(blueprint: def-sfb-proper-scheme-stalk-tangent-data). -/
structure ClosedCompletionCompatibility (C : Coherence.{u})
    (D : TopCat.SheafCotangent.Comparison C) (f : X ⟶ Spec (.of k))
    (T : TangentIdentification C D f) where
  comparison : ∀ (x : X), IsClosed ({x} : Set X) → StalkComparison C D f x
  completed : ∀ (x : X) (_hx : IsClosed ({x} : Set X))
    (P : Naive.Presentation (SchemeDeformation.affineArrow k (localAlgebra f x)))
    (_hP : Naive.IsLocalizedPolynomial P)
    (_hF : CompletedSchemeTangent.IsFiniteLocalizedPolynomial P),
    CompletedSchemeTangent.Comparison P
  stalk_exists : ∀ (x : X) (_hx : IsClosed ({x} : Set X))
    (Y : SchemeDeformation.Lift f
      (SchemeDeformation.directionReduction k (ModuleCat.of k k))),
    ∃ Q : Algebra.FlatDeformation.Groupoid (localAlgebra f x)
      (ArtinDeformation.squareZeroTest (R := k) (k := k) k),
      Nonempty (IsStalkDeformation f x Y Q)
  ext_representatives : ∀ (x : X) (_hx : IsClosed ({x} : Set X))
    (κ : Naive.Comparison C)
    (P : Naive.Presentation (SchemeDeformation.affineArrow k (localAlgebra f x)))
    (hP : Naive.IsLocalizedPolynomial P),
    Function.Surjective (fun η : DerivedCategory.Q.obj (Naive.complex P) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (localAlgebra f x)) 0).obj
        (ModuleCat.of (localAlgebra f x) (localAlgebra f x)))⟦(1 : ℤ)⟧ ↦
      κ.comparison P hP ≫ η)
  commutes : ∀ (x : X) (hx : IsClosed ({x} : Set X))
    (_hN : IsNoetherianRing (localAlgebra f x))
    (κ : Naive.Comparison C)
    (P : Naive.Presentation (SchemeDeformation.affineArrow k (localAlgebra f x)))
    (hP : Naive.IsLocalizedPolynomial P)
    (hF : CompletedSchemeTangent.IsFiniteLocalizedPolynomial P)
    (Y : SchemeDeformation.Lift f
      (SchemeDeformation.directionReduction k (ModuleCat.of k k)))
    (Q : Algebra.FlatDeformation.Groupoid (localAlgebra f x)
      (ArtinDeformation.squareZeroTest (R := k) (k := k) k)),
    Nonempty (IsStalkDeformation f x Y Q) →
    ∀ η : DerivedCategory.Q.obj (Naive.complex P) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (localAlgebra f x)) 0).obj
        (ModuleCat.of (localAlgebra f x) (localAlgebra f x)))⟦(1 : ℤ)⟧,
    κ.comparison P hP ≫ η = (comparison x hx).ext (T.identify Y.class) →
    (completed x hx P hP hF).classify ((completed x hx P hP hF).completion ⟦Q⟧) =
      @CompletedSchemeTangent.extMap k (localAlgebra f x) _ _ _ _ _hN
        (inferInstanceAs (HasDerivedCategory.{u + 1}
          (ModuleCat.{u} (CommRingCat.of (localAlgebra f x)))))
        (inferInstanceAs (HasDerivedCategory.{u + 1}
          (ModuleCat.{u} (CommRingCat.of (CompletedSchemeTangent.Completion (localAlgebra f x))))))
        P η

end AlgebraicGeometry.ProperSchemeDeformation
