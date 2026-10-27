module

public import Sheaf.Paper.ProEtaleProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal

/-! # Canonical pro-etale ordered integration arrows
Source: main-20261015 vector-bundle integration and projective-line normalization
(blueprint: def-pur-finite-site-tensor-projection).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

section Generic
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
/-- The canonical Koszul symmetry, descended from the signed swap of K-flat complexes.
Source: Stacks 06YU (blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def symmetry (T : Scheme.{u}) : derivedTensor B T ≅
    (derivedTensor B T).flip :=
  DerivedCategory.canonicalTensorSymmetry
    (Sheaf (Scheme.ProEt.topology T) B)

/-- The coefficient-first projection map of the pro-etale compactification.
The two symmetries only put the coefficient first; the middle map is the
published proper-counit/open-adjunct compact-support projection.
Source: Stacks 0944 and 0GL1
(blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def projection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B)) :
    ((derivedTensor B Y).obj K).obj
      ((rightDerivedLowerShriekOfCompactification B c).obj W) ⟶
    (rightDerivedLowerShriekOfCompactification B c).obj
      (((derivedTensor B X).obj ((upperStar B f).leftDerivedFunctor.obj K)).obj W) :=
  ((symmetry B Y).hom.app K).app _ ≫
    ((projectionMapOfCompactification B c).app W).app K ≫
    (rightDerivedLowerShriekOfCompactification B c).map
      (((symmetry B X).hom.app W).app _)




end Generic

/-- Canonical tensor comparison for the exact inverse image.
Source: Stacks 099R (blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def tensorComparison (T : Scheme.{u})
    (K L : Etale.DerivedCategoryModule A T) :
    (comparison A T).obj (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj L) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj ((comparison A T).obj K)).obj
        ((comparison A T).obj L) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} A) K).app L

/-- The constant right unitor, in the same comparison coordinates as the trace.
Source: unit-normalized tensor comparison
(blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def rightUnit (T : Scheme.{u}) (K : Etale.DerivedCategoryModule A T) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj ((comparison A T).obj K)).obj
      (unit A T) ≅ (comparison A T).obj K :=
  (tensorComparison A T K (Etale.ordinaryFiniteUnit A T)).symm ≪≫
    (comparison A T).mapIso (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} A) T K)

section Generic
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
/-- Coefficient-first proper projection, formed from the actual adjoint-of-counit map.
Source: Stacks 0GL1 (blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def properProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B)) :
    ((derivedTensor B Y).obj K).obj ((lowerStar B f).rightDerivedFunctor.obj W) ⟶
    (lowerStar B f).rightDerivedFunctor.obj
      (((derivedTensor B X).obj ((upperStar B f).leftDerivedFunctor.obj K)).obj W) :=
  ((symmetry B Y).hom.app K).app _ ≫
    ((rightDerivedLowerStarProjectionMap B f).app W).app K ≫
    (lowerStar B f).rightDerivedFunctor.map
      (((symmetry B X).hom.app W).app _)

end Generic

/-- Canonical source comparison for a pullback tensor, before any specialization
of the coefficient ring or of the Tate line.
Source: Stacks 099R (blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def tensorPullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Etale.DerivedCategoryModule A Y) (W : Etale.DerivedCategoryModule A X) :
    (comparison A X).obj
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFinitePullback A f).obj K)).obj W) ≅
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
        ((comparison A Y).obj K))).obj ((comparison A X).obj W) :=
  tensorComparison A X _ W ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso ((pullback A f).app K)).app _

/-- The Hom type of a proper integration, cached before specializing coefficients.
Source: Stacks 0GL1 (blueprint: def-pur-finite-site-tensor-projection). -/
@[implicit_reducible]
def ProperIntegrationHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : Etale.DerivedCategoryModule A Y) :=
  (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
        ((comparison A Y).obj K))).obj W) ⟶ (comparison A Y).obj K

/-- Apply the geometric inverse-image comparison and then a prescribed right-object iso.
Source: Stacks 099R (blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def pullbackThen {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : Etale.DerivedCategoryModule A Y)
    (Z : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : (comparison A Y).obj W ≅ Z) :=
  (pullback A f).app W ≪≫
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.mapIso e

/-- Inverse proper projection followed by tensor trace and the normalized constant unit.
Source: Stacks 0GL1 (blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def properIntegration {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : Etale.DerivedCategoryModule A Y)
    (t : (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj W ⟶ unit A Y)
    (hp : IsIso (properProjection (ModuleCat.{u + 1} A) f W ((comparison A Y).obj K))) :
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((comparison A Y).obj K))).obj W) ⟶ (comparison A Y).obj K :=
  letI := hp
  inv (properProjection (ModuleCat.{u + 1} A) f W ((comparison A Y).obj K)) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((comparison A Y).obj K)).map t ≫
      (rightUnit A Y K).hom

/-- The defining counit equation for inverse projection and a prescribed trace.
Source: Stacks 0GL1 (blueprint: def-pur-finite-site-tensor-projection). -/
def ProperIntegrationEquation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : Etale.DerivedCategoryModule A Y)
    (t : (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj W ⟶ unit A Y)
    (e : ProperIntegrationHom A f W K) : Prop :=
  properProjection (ModuleCat.{u + 1} A) f W ((comparison A Y).obj K) ≫ e =
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((comparison A Y).obj K)).map t ≫
      (rightUnit A Y K).hom

/-- Compose a specified inverse projection with ordinary tensor integration.
Source: vector-bundle integration formula
(blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def ordinaryTensorIntegrate (T : Scheme.{u})
    (K W Z : Etale.DerivedCategoryModule A T)
    (p : Z ≅ ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj W)
    (t : W ⟶ Etale.ordinaryFiniteUnit A T) : Z ⟶ K :=
  p.hom ≫ ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K).map t ≫
    (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} A) T K).hom

/-- Compose a specified inverse projection with pro-etale tensor integration.
Source: vector-bundle integration formula
(blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def proTensorIntegrate (T : Scheme.{u}) (K : Etale.DerivedCategoryModule A T)
    (W Z : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (p : Z ≅ ((derivedTensor (ModuleCat.{u + 1} A) T).obj ((comparison A T).obj K)).obj W)
    (t : W ⟶ unit A T) : Z ⟶ (comparison A T).obj K :=
  p.hom ≫ ((derivedTensor (ModuleCat.{u + 1} A) T).obj ((comparison A T).obj K)).map t ≫
    (rightUnit A T K).hom

/-- Coefficient specialization of the published compact-support projection.
Source: Stacks 0GL1 (blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def moduleProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :=
  projection (ModuleCat.{u + 1} A) c ((comparison A X).obj W) ((comparison A Y).obj K)

/-- Compact-support projection in comparison-source coordinates.
Source: Stacks 099R and 0GL1 (blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def comparedModuleProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :=
  moduleProjection A c W K ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (tensorPullbackComparison A f K W).inv

/-- Select the uniquely specified datum without expanding its geometric property.
Source: unique characterization convention for canonical constructions
(blueprint: def-pur-finite-site-tensor-projection). -/
@[irreducible]
def uniqueValue {α : Sort v} (P : α → Prop) (h : ∃! a, P a) : α :=
  h.exists.choose

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
