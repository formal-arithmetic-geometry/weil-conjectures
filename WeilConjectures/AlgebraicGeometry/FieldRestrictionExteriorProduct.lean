/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
public import WeilConjectures.AlgebraicGeometry.EtaleUnboundedRestrictionComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Constant
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafCompose
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

import WeilConjectures.SixFunctors.EtaleUnboundedRestrictionAdjunct
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf

/-!
# Field restriction and the canonical ordinary exterior product

Source: Stacks Project, Tag 0F1E, remark-define-kunneth-map, and Tag 0FPI,
lemma-adjoints-push-pull-compatibility
(blueprint: lem-pur-exterior-product-field-restriction).

## Main definitions

- `RestrictionTensorData`: the balanced quotient, normalized on total complexes.
- `fieldRestrictionSectionsMap`: the canonical mate of restriction of constant complexes.
- `RestrictionSectionsData`: its normalized isomorphism and exactness assertions.
- `fieldRestrictionUnbalancedExterior`: the product before the balanced quotient.
- `fieldRestrictionInputAction`: the two independent coefficient actions.
- `FieldRestrictionExteriorProductData`: the complete normalized compatibility assertion.

## Main statements

- `fieldRestrictionExteriorProduct`: restriction compatibility, independent scalar actions,
  preservation of split retracts, and conservativity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section TensorData
variable {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  [MonoidalClosed C] [MonoidalClosed D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
  [MonoidalCategory (DerivedCategory C)] [MonoidalCategory (DerivedCategory D)]
  [(DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).LaxMonoidal]
  [(DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D).LaxMonoidal]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ordinary : G.LaxMonoidal)

/-- Balanced derived restriction tensorator, including its naturality and its normalization
on every total-tensor summand and at localization. The parameter `ordinary` is the existing
restriction tensorator, not an arbitrary bilinear map. Its value is `x ⊗ y ↦ x ⊗ y` with
balancing changed from F to B. The localization square determines the morphism on K-flat
representatives. Source: Stacks 0F1E and 0FPI
(blueprint: lem-pur-exterior-product-field-restriction). -/
structure RestrictionTensorData where
  map : ∀ P Q : DerivedCategory C,
    G.mapDerivedCategory.obj P ⊗ G.mapDerivedCategory.obj Q ⟶
      G.mapDerivedCategory.obj (P ⊗ Q)
  naturality : ∀ {P P' Q Q' : DerivedCategory C} (a : P ⟶ P') (b : Q ⟶ Q'),
    (G.mapDerivedCategory.map a ⊗ₘ G.mapDerivedCategory.map b) ≫ map P' Q' =
      map P Q ≫ G.mapDerivedCategory.map (a ⊗ₘ b)
  chain : ∀ K L : CochainComplex C ℤ,
    (G.mapHomologicalComplex (.up ℤ)).obj K ⊗
      (G.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (G.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L)
  chain_summand : ∀ (K L : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫ (chain K L).f n =
      ordinary.μ (K.X p) (L.X q) ≫ G.map (HomologicalComplex.ιTensorObj K L p q n h)
  normalization : ∀ K L : CochainComplex C ℤ,
    map (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L) ≫
        G.mapDerivedCategoryFactors.hom.app (K ⊗ L) =
      (G.mapDerivedCategoryFactors.hom.app K ⊗ₘ G.mapDerivedCategoryFactors.hom.app L) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L) ≫
        DerivedCategory.Q.map (chain K L)

end TensorData

/-- The canonical map from restricted B-valued derived sections to F-valued derived
sections of the restricted complex. It is the mate of the canonical restriction square
for constant complexes, fixing its normalization. Source: Stacks 0FPI
(blueprint: lem-pur-exterior-product-field-restriction). -/
def fieldRestrictionSectionsMap
    {F B : Type (u + 1)} [CommRing F] [CommRing B] (φ : F →+* B)
    (T : Scheme.{u}) :
    rightDerivedGlobalSections (ModuleCat.{u + 1} B) T ⋙
        (ModuleCat.restrictScalars φ).mapDerivedCategory ⟶
      Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} F) T :=
  mateEquiv (derivedConstantSheafAdjunction (ModuleCat.{u + 1} B) T)
    (derivedConstantSheafAdjunction (ModuleCat.{u + 1} F) T)
    (Functor.mapDerivedCategorySquareIso
      (constantSheafCompSheafComposeIso T.smallEtaleTopology
        (ModuleCat.restrictScalars φ)).symm).hom


/-- Canonical restriction/sections comparison, including its coefficient and retract
compatibility and reflection of zero objects and isomorphisms. Naturality is part of the
natural isomorphism; the split equations explicitly record the transported splitting.
Source: Stacks 0FPI (blueprint: lem-pur-exterior-product-field-restriction). -/
structure RestrictionSectionsData
    {F B : Type (u + 1)} [CommRing F] [CommRing B] (φ : F →+* B)
    (T : Scheme.{u}) where
  iso : Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ⋙
      rightDerivedGlobalSections (ModuleCat.{u + 1} F) T ≅
    rightDerivedGlobalSections (ModuleCat.{u + 1} B) T ⋙
      (ModuleCat.restrictScalars φ).mapDerivedCategory
  normalization : iso.inv = fieldRestrictionSectionsMap φ T
  coefficient : ∀ (H : DerivedCategoryModule B T) (b : B),
    (rightDerivedGlobalSections (ModuleCat.{u + 1} F) T).map
        ((Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map (b • 𝟙 H)) ≫
        iso.hom.app H =
      iso.hom.app H ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) T).map (b • 𝟙 H))
  split : ∀ (H Z : DerivedCategoryModule B T) (i : Z ⟶ H) (p : H ⟶ Z),
    i ≫ p = 𝟙 Z →
    (rightDerivedGlobalSections (ModuleCat.{u + 1} F) T).map
        ((Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map i) ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} F) T).map
        ((Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map p) = 𝟙 _ ∧
    (ModuleCat.restrictScalars φ).mapDerivedCategory.map
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) T).map i) ≫
      (ModuleCat.restrictScalars φ).mapDerivedCategory.map
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) T).map p) = 𝟙 _
  detects_zero : ∀ H : DerivedCategoryModule B T,
    IsZero ((Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).obj H) ↔ IsZero H
  detects_iso : ∀ (H H' : DerivedCategoryModule B T) (a : H ⟶ H'),
    IsIso ((Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map a) ↔ IsIso a

attribute [instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

/-- The F-valued exterior product before balancing, with the canonical exact
restriction/pullback identifications inserted. Source: Stacks 0F1E and 0FPI
(blueprint: lem-pur-exterior-product-field-restriction). -/
def fieldRestrictionUnbalancedExterior
    {F B : Type (u + 1)} [CommRing F] [CommRing B] (φ : F →+* B)
    {k : Type u} [Field k] [IsSepClosed k] {X Y W : Scheme.{u}}
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (w : q ≫ g = p ≫ f) (K : DerivedCategoryModule B X) (L : DerivedCategoryModule B Y) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} F) X).obj
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj K) ⊗
      (rightDerivedGlobalSections (ModuleCat.{u + 1} F) Y).obj
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).obj L) ⟶
    (rightDerivedGlobalSections (ModuleCat.{u + 1} F) W).obj
      ((Sheaf.derivedRestrictScalars W.smallEtaleTopology φ).obj
          ((L(upperStar (ModuleCat.{u + 1} B) p)).obj K) ⊗
        (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ).obj
          ((L(upperStar (ModuleCat.{u + 1} B) q)).obj L)) :=
  kunnethGlobalSectionsMap F p q f g w
      ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj K)
      ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).obj L) ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} F) W).map
      ((scalarRestrictionPullbackIso φ p).hom.app K ⊗ₘ
        (scalarRestrictionPullbackIso φ q).hom.app L)

/-- The two independent input coefficient actions on F-valued sections. Checking all
`a,b : B` checks the generators `a ⊗ b` of `B ⊗[F] B`; no diagonal balancing has yet
been imposed. Source: Stacks 0F1E, naturality of its counit composite
(blueprint: lem-pur-exterior-product-field-restriction). -/
def fieldRestrictionInputAction
    {F B : Type (u + 1)} [CommRing F] [CommRing B] (φ : F →+* B)
    {X Y : Scheme.{u}} (K : DerivedCategoryModule B X) (L : DerivedCategoryModule B Y)
    (a b : B) :
    End ((rightDerivedGlobalSections (ModuleCat.{u + 1} F) X).obj
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj K) ⊗
      (rightDerivedGlobalSections (ModuleCat.{u + 1} F) Y).obj
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).obj L)) :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} F) X).map
      ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map (a • 𝟙 K)) ⊗ₘ
    (rightDerivedGlobalSections (ModuleCat.{u + 1} F) Y).map
      ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map (b • 𝟙 L))


/-- All the data and assertions of the field-restriction exterior-product square.
The tensor comparisons are fixed by their ordinary balanced-quotient normalization, and
sections comparisons by the adjunction mate. The two linearity fields are the two
`B ⊗[F] B`-linearity assertions before applying the balancing maps.
Source: Stacks 0F1E and 0FPI; the coefficient-restriction step in the first paragraph
of the blueprint proof of `lem-pur-ordinary-kunneth-finite-ring`
(blueprint: lem-pur-exterior-product-field-restriction). -/
structure FieldRestrictionExteriorProductData
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) where
  sectionsX : RestrictionSectionsData (algebraMap F B) X
  sectionsY : RestrictionSectionsData (algebraMap F B) Y
  sectionsW : RestrictionSectionsData (algebraMap F B) (pullback f g)
  tensorX : RestrictionTensorData
    (Sheaf.restrictScalars X.smallEtaleTopology (algebraMap F B))
    (sheafComposeLaxMonoidal X.smallEtaleTopology (ModuleCat.restrictScalars (algebraMap F B)))
  tensorY : RestrictionTensorData
    (Sheaf.restrictScalars Y.smallEtaleTopology (algebraMap F B))
    (sheafComposeLaxMonoidal Y.smallEtaleTopology (ModuleCat.restrictScalars (algebraMap F B)))
  tensorW : RestrictionTensorData
    (Sheaf.restrictScalars (pullback f g).smallEtaleTopology (algebraMap F B))
    (sheafComposeLaxMonoidal (pullback f g).smallEtaleTopology
      (ModuleCat.restrictScalars (algebraMap F B)))
  tensor0 : RestrictionTensorData (ModuleCat.restrictScalars (algebraMap F B)) inferInstance
  square : ∀ (K : DerivedCategoryModule B X) (L : DerivedCategoryModule B Y),
    fieldRestrictionUnbalancedExterior (algebraMap F B)
        (pullback.fst f g) (pullback.snd f g) f g pullback.condition.symm K L ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} F) (pullback f g)).map
        (tensorW.map ((L(upperStar (ModuleCat.{u + 1} B) (pullback.fst f g))).obj K)
          ((L(upperStar (ModuleCat.{u + 1} B) (pullback.snd f g))).obj L)) ≫
      sectionsW.iso.hom.app
        (((L(upperStar (ModuleCat.{u + 1} B) (pullback.fst f g))).obj K) ⊗
          ((L(upperStar (ModuleCat.{u + 1} B) (pullback.snd f g))).obj L)) =
    (sectionsX.iso.hom.app K ⊗ₘ sectionsY.iso.hom.app L) ≫
      tensor0.map ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) X).obj K)
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) Y).obj L) ≫
      (ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.map
        (kunnethGlobalSectionsMap B (pullback.fst f g) (pullback.snd f g) f g
          pullback.condition.symm K L)
  linearity_left : ∀ (K : DerivedCategoryModule B X) (L : DerivedCategoryModule B Y)
      (a b : B),
    fieldRestrictionInputAction (algebraMap F B) K L a b ≫
      fieldRestrictionUnbalancedExterior (algebraMap F B)
        (pullback.fst f g) (pullback.snd f g) f g pullback.condition.symm K L =
    fieldRestrictionUnbalancedExterior (algebraMap F B)
        (pullback.fst f g) (pullback.snd f g) f g pullback.condition.symm K L ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} F) (pullback f g)).map
        ((Sheaf.derivedRestrictScalars (pullback f g).smallEtaleTopology
            (algebraMap F B)).map
            ((L(upperStar (ModuleCat.{u + 1} B) (pullback.fst f g))).map (a • 𝟙 K)) ⊗ₘ
          (Sheaf.derivedRestrictScalars (pullback f g).smallEtaleTopology
            (algebraMap F B)).map
            ((L(upperStar (ModuleCat.{u + 1} B) (pullback.snd f g))).map (b • 𝟙 L)))
  linearity_right : ∀ (K : DerivedCategoryModule B X) (L : DerivedCategoryModule B Y)
      (a b : B),
    fieldRestrictionInputAction (algebraMap F B) K L a b ≫
      (sectionsX.iso.hom.app K ⊗ₘ sectionsY.iso.hom.app L) =
    (sectionsX.iso.hom.app K ⊗ₘ sectionsY.iso.hom.app L) ≫
      ((ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.map
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) X).map (a • 𝟙 K)) ⊗ₘ
        (ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.map
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) Y).map (b • 𝟙 L)))
  detects_zero0 : ∀ H : DerivedCategory (ModuleCat.{u + 1} B),
    IsZero ((ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.obj H) ↔ IsZero H
  detects_iso0 : ∀ (H H' : DerivedCategory (ModuleCat.{u + 1} B)) (a : H ⟶ H'),
    IsIso ((ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.map a) ↔ IsIso a


/-- The three sections comparisons needed for the exterior-product square. This package is
strictly the sections part of `FieldRestrictionExteriorProductData`; its construction is the
unbounded restriction-adjunct argument of the first proof step.
(blueprint: lem-pur-field-restriction-sections-package). -/
structure FieldRestrictionSectionsPackage
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) where
  sectionsX : RestrictionSectionsData (algebraMap F B) X
  sectionsY : RestrictionSectionsData (algebraMap F B) Y
  sectionsW : RestrictionSectionsData (algebraMap F B) (pullback f g)

/-- Existence of the sections part of the field-restriction package.
Source: Stacks 0FPI, restriction/direct-image compatibility; the four-step proof of
`lem-pur-exterior-product-field-restriction`, step 1.

Proof. Fix `T ∈ {X, Y, X ×ₖ Y}` with structure map `c_T : T ⟶ Spec k`. The unbounded étale
restriction-adjunct comparison (`lem-sf-etale-unbounded-restriction-adjunct`) gives a natural
isomorphism `v_T : U_{Spec k} Rc_{T*,B} ≅ Rc_{T*,F} U_T`, since restriction of scalars does not
change the underlying abelian sheaves and `Rc_*` is computed on them. As `k` is separably closed,
the constant-sheaf functor on `(Spec k)_et` is an equivalence
(`lem-pur-point-constant-equivalence`); its exact quasi-inverse, sections over `Spec k`, commutes
with termwise restriction, and `Γ(Spec k, c_{T*} I) = Γ(T, I)` on K-injective `I`. Taking sections
of `v_T` gives a natural isomorphism `U_0 RΓ_B(T, -) ≅ RΓ_F(T, U_T -)`; it is the mate of the
restriction square for constant complexes, i.e. `fieldRestrictionSectionsMap`, so its inverse is
the `iso` of `RestrictionSectionsData` with the required normalization. Coefficient compatibility
is naturality applied to `b • 𝟙 H`; the split equations are functoriality applied to `i ≫ p = 𝟙`;
termwise restriction leaves underlying complexes and chain maps unchanged, so it preserves and
reflects acyclicity of cones, hence detects zero objects and isomorphisms.
(blueprint: lem-pur-field-restriction-sections-package). -/
theorem fieldRestrictionSectionsPackage
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) :
    Nonempty (FieldRestrictionSectionsPackage F B f g) := by
  sorry

/-- The four normalized tensorators needed for the exterior-product square. This package is
strictly the tensor part of `FieldRestrictionExteriorProductData`; it records no sections,
square, linearity, or conservativity assertions.
(blueprint: lem-pur-field-restriction-tensor-package). -/
structure FieldRestrictionTensorPackage
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) where
  tensorX : RestrictionTensorData
    (Sheaf.restrictScalars X.smallEtaleTopology (algebraMap F B))
    (sheafComposeLaxMonoidal X.smallEtaleTopology (ModuleCat.restrictScalars (algebraMap F B)))
  tensorY : RestrictionTensorData
    (Sheaf.restrictScalars Y.smallEtaleTopology (algebraMap F B))
    (sheafComposeLaxMonoidal Y.smallEtaleTopology (ModuleCat.restrictScalars (algebraMap F B)))
  tensorW : RestrictionTensorData
    (Sheaf.restrictScalars (pullback f g).smallEtaleTopology (algebraMap F B))
    (sheafComposeLaxMonoidal (pullback f g).smallEtaleTopology
      (ModuleCat.restrictScalars (algebraMap F B)))
  tensor0 : RestrictionTensorData (ModuleCat.restrictScalars (algebraMap F B)) inferInstance

/-- Existence of the normalized tensorator part of the field-restriction package.
Source: Stacks 0F1E, total-complex balanced quotient; the four-step proof of
`lem-pur-exterior-product-field-restriction`, step 2.

Proof. On each of the four abelian categories (étale sheaves of `B`-modules on `X`, `Y`,
`X ×ₖ Y`, and `B`-modules) the restriction functor `G` is exact and lax monoidal through the
balanced quotient `x ⊗_F y ↦ x ⊗_B y`. Define `chain K L` on the summand `(p, q)` of the total
tensor complex as `μ (K.X p) (L.X q) ≫ G.map ι_{p,q}`; these summands are compatible with the
differentials (the quotient is natural and preserves the signs), and the summand equation holds
by construction. Every complex has a K-flat resolution, and a K-flat `B`-complex stays K-flat
over `F` because `B` is free over `F`; on K-flat representatives `μ_Q` is an isomorphism, so
the localization square `normalization` defines `map (Q K) (Q L)`, independently of the
representative. Transport along isomorphisms `P ≅ Q K` defines `map P Q` for all objects and gives
naturality.
(blueprint: lem-pur-field-restriction-tensor-package). -/
theorem fieldRestrictionTensorPackage
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) :
    Nonempty (FieldRestrictionTensorPackage F B f g) := by
  sorry

/-- The square, two coefficient actions, and point conservativity assertions, after the
sections and tensor packages have been supplied. This is a strict compatibility fragment of
`FieldRestrictionExteriorProductData`, and is independent of the existence proofs for those
packages.
(blueprint: lem-pur-field-restriction-compatibility-package). -/
structure FieldRestrictionCompatibilityPackage
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (s : FieldRestrictionSectionsPackage F B f g)
    (t : FieldRestrictionTensorPackage F B f g) where
  square : ∀ (K : DerivedCategoryModule B X) (L : DerivedCategoryModule B Y),
    fieldRestrictionUnbalancedExterior (algebraMap F B)
        (pullback.fst f g) (pullback.snd f g) f g pullback.condition.symm K L ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} F) (pullback f g)).map
        (t.tensorW.map ((L(upperStar (ModuleCat.{u + 1} B) (pullback.fst f g))).obj K)
          ((L(upperStar (ModuleCat.{u + 1} B) (pullback.snd f g))).obj L)) ≫
      s.sectionsW.iso.hom.app
        (((L(upperStar (ModuleCat.{u + 1} B) (pullback.fst f g))).obj K) ⊗
          ((L(upperStar (ModuleCat.{u + 1} B) (pullback.snd f g))).obj L)) =
    (s.sectionsX.iso.hom.app K ⊗ₘ s.sectionsY.iso.hom.app L) ≫
      t.tensor0.map ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) X).obj K)
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) Y).obj L) ≫
      (ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.map
        (kunnethGlobalSectionsMap B (pullback.fst f g) (pullback.snd f g) f g
          pullback.condition.symm K L)
  linearity_left : ∀ (K : DerivedCategoryModule B X) (L : DerivedCategoryModule B Y)
      (a b : B),
    fieldRestrictionInputAction (algebraMap F B) K L a b ≫
      fieldRestrictionUnbalancedExterior (algebraMap F B)
        (pullback.fst f g) (pullback.snd f g) f g pullback.condition.symm K L =
    fieldRestrictionUnbalancedExterior (algebraMap F B)
        (pullback.fst f g) (pullback.snd f g) f g pullback.condition.symm K L ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} F) (pullback f g)).map
        ((Sheaf.derivedRestrictScalars (pullback f g).smallEtaleTopology
            (algebraMap F B)).map
            ((L(upperStar (ModuleCat.{u + 1} B) (pullback.fst f g))).map (a • 𝟙 K)) ⊗ₘ
          (Sheaf.derivedRestrictScalars (pullback f g).smallEtaleTopology
            (algebraMap F B)).map
            ((L(upperStar (ModuleCat.{u + 1} B) (pullback.snd f g))).map (b • 𝟙 L)))
  linearity_right : ∀ (K : DerivedCategoryModule B X) (L : DerivedCategoryModule B Y)
      (a b : B),
    fieldRestrictionInputAction (algebraMap F B) K L a b ≫
      (s.sectionsX.iso.hom.app K ⊗ₘ s.sectionsY.iso.hom.app L) =
    (s.sectionsX.iso.hom.app K ⊗ₘ s.sectionsY.iso.hom.app L) ≫
      ((ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.map
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) X).map (a • 𝟙 K)) ⊗ₘ
        (ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.map
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) Y).map (b • 𝟙 L)))
  detects_zero0 : ∀ H : DerivedCategory (ModuleCat.{u + 1} B),
    IsZero ((ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.obj H) ↔ IsZero H
  detects_iso0 : ∀ (H H' : DerivedCategory (ModuleCat.{u + 1} B)) (a : H ⟶ H'),
    IsIso ((ModuleCat.restrictScalars (algebraMap F B)).mapDerivedCategory.map a) ↔ IsIso a

/-- Existence of the compatibility fragment. Its proof is the adjunction, monoidality and
Kunneth-naturality argument in steps 2--4 of the reviewed proof plan.
Source: Stacks 0F1E and 0FPI.

Proof. The packages `s` and `t` are determined by their normalizations (`s` by
`iso.inv = fieldRestrictionSectionsMap`, `t` on K-flat representatives), so it suffices to treat
the canonical ones. Square: let `c : W ⟶ Spec k` and let `α_F, α_B` be the maps whose
`c⁻¹ ⊣ Rc_*` adjoints are the two counit-defined exterior products. The adjunct identity of
`lem-sf-etale-unbounded-restriction-adjunct` compares the counits of `f` and `g` over `F` and
`B`; the composition and pullback identifications are the identity on underlying sheaves; and
inverse-image monoidality (`lem-kun-inverse-image-monoidal`) commutes with the balanced quotient,
since on K-flat representatives both composites are `c⁻¹x ⊗_F c⁻¹y ↦ c⁻¹(x ⊗_B y)`. Hence
`U_W(α_B) ∘ a ∘ c⁻¹(b_S ∘ (v_X⁻¹ ⊗ v_Y⁻¹)) = b_W ∘ (a_p ⊗ a_q) ∘ α_F`; transposing along
`c⁻¹ ⊣ Rc_*` (again the adjunct identity) and taking sections over `Spec k` as in the sections
package turns this into `square`. Linearity: the endomorphisms `a • 𝟙`, `b • 𝟙` of the two inputs
commute with each factor before the balanced quotients, by naturality of the Kunneth map
(`lem-kun-kunneth-map-natural`), of the pullback identifications, and of the sections
isomorphisms. Point conservativity: restriction of scalars on complexes of `B`-modules leaves
underlying complexes unchanged, so it preserves and reflects acyclic cones.
(blueprint: lem-pur-field-restriction-compatibility-package). -/
theorem fieldRestrictionCompatibilityPackage
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (s : FieldRestrictionSectionsPackage F B f g)
    (t : FieldRestrictionTensorPackage F B f g) :
    Nonempty (FieldRestrictionCompatibilityPackage F B f g s t) := by
  sorry

/-- Field restriction commutes with the counit-defined ordinary exterior product, with
its canonical comparisons, independent coefficient actions, split idempotents, and
conservativity. There is no boundedness, finiteness, cohomological-dimension or Kunneth
isomorphism assumption.
Source: Stacks 0F1E and 0FPI; blueprint proof of
`lem-pur-ordinary-kunneth-finite-ring`, first finite-field paragraph
(blueprint: lem-pur-exterior-product-field-restriction).

Proof: Restriction is exact termwise. Apply the unbounded etale restriction-adjunct
comparison to each structure map to Spec k. Sections at the separably closed point is
an exact equivalence commuting with restriction; its application to that comparison
is the inverse of `fieldRestrictionSectionsMap`, by the constant-sheaf adjunction.
For the tensorators use K-flat B-representatives. They stay K-flat over F because B is
free over F. The quotient on each total-tensor summand is x tensor y mapping to
x tensor y, changing only the balancing ring. This gives the stated localization
normalization and naturality. Compare the adjoints defining the two Kunneth maps.
The restriction-adjunct identity identifies their counits; the composition and
pullback comparisons are identity on underlying sheaves; inverse-image monoidality
commutes with the quotient on every K-flat summand. Transposing this equality and
taking sections over Spec k gives `square`. Naturality applied separately to the
two coefficient multiplications gives both independent-action identities before
balancing. Naturality of the sections isomorphisms gives coefficient compatibility;
functoriality transports every split retract and its idempotent. Finally restriction
leaves underlying cohomology sheaves and modules unchanged, so it detects vanishing
and, by the cone criterion, isomorphisms. These arguments use unbounded resolutions
and impose none of the excluded finiteness assumptions. -/
theorem fieldRestrictionExteriorProduct
    (F B : Type (u + 1)) [Field F] [Field B] [Algebra F B]
    {k : Type u} [Field k] [IsSepClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) :
    Nonempty (FieldRestrictionExteriorProductData F B f g) := by
  classical
  obtain ⟨s⟩ := fieldRestrictionSectionsPackage F B f g
  obtain ⟨t⟩ := fieldRestrictionTensorPackage F B f g
  obtain ⟨c⟩ := fieldRestrictionCompatibilityPackage F B f g s t
  exact ⟨{ sectionsX := s.sectionsX,
            sectionsY := s.sectionsY,
            sectionsW := s.sectionsW,
            tensorX := t.tensorX,
            tensorY := t.tensorY,
            tensorW := t.tensorW,
            tensor0 := t.tensor0,
            square := c.square,
            linearity_left := c.linearity_left,
            linearity_right := c.linearity_right,
            detects_zero0 := c.detects_zero0,
            detects_iso0 := c.detects_iso0 }⟩

end AlgebraicGeometry.Etale
