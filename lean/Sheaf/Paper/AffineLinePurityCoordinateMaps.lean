module

public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula

/-! # Canonical coordinate maps for affine-line purity

Source: main-20261015, sec-smooth-purity/sk-prop-an,
affine-line purity comparison, order 2318 (blueprint: def-pur-affine-line-purity-coordinate-maps).

The exact comparison unit, tensor trace composite, actual open-counit trace
restriction, and canonical inverse-image/tensor realization comparisons. No
map of the required type is chosen arbitrarily.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineLinePurity

open VectorIntegrationSite

section Unit
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]

/-- Canonical coefficient-unit comparison. Source: exact monoidal comparison
(blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def coefficientUnitIso (T : Scheme.{u}) :
    (comparisonUpperStar B T).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (Sheaf T.smallEtaleTopology B))) ≅
        𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology T) B)) :=
  ((comparisonUpperStar B T).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (comparisonUpperStar B T)).symm ≪≫
    DerivedCategory.singleFunctorObjUnitIso _

/-- The monoidal right unitor with the compared constant coefficient unit.
Source: derived tensor unit (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def coefficientRightUnit (T : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) B)) :
    ((derivedTensor B T).obj K).obj
      ((comparisonUpperStar B T).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (Sheaf T.smallEtaleTopology B)))) ≅ K :=
  ((derivedTensor B T).obj K).mapIso (coefficientUnitIso B T) ≪≫
    (CategoryTheory.MonoidalCategory.rightUnitor K)

/-- Compose inverse projection, tensor of a prescribed trace and the coefficient unitor.
The application below supplies the canonical inverse projection and canonical integration.
Source: a_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def tensorTrace (T : Scheme.{u})
    (K Z W : DerivedCategory (Sheaf (Scheme.ProEt.topology T) B))
    (e : Z ≅ ((derivedTensor B T).obj K).obj W)
    (t : W ⟶ (comparisonUpperStar B T).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (Sheaf T.smallEtaleTopology B)))) :
    Z ⟶ K :=
  e.hom ≫ ((derivedTensor B T).obj K).map t ≫ (coefficientRightUnit B T K).hom

end Unit

/-- Restriction of a prescribed projective trace by the actual open counit.
This helper is instantiated below with the normalized projective-line trace.
Source: affine-line integration display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def restrictTrace (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (W : Etale.DerivedCategoryModule A (ProjectiveLine T))
    (t : (lowerStar (ModuleCat.{u + 1} A)
      (ProjectiveLine T ↘ T)).rightDerivedFunctor.obj
        ((comparison A (ProjectiveLine T)).obj W) ⟶ unit A T) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T)).obj
        ((comparison A (AffineSpace PUnit.{u + 1} T)).obj
          ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T)).obj W)) ⟶
      unit A T :=
  (lineLeft A T).map ((pullback A (ProjectiveLine.affineChart T)).app W).hom ≫
    (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine T ↘ T)).rightDerivedFunctor.map
      ((openAdjunction A (ProjectiveLine.affineChart T)).counit.app
        ((comparison A (ProjectiveLine T)).obj W)) ≫ t

/-- Compare the canonical shifted ordinary Tate pullback, before coefficient specialization.
Source: canonical Tate inverse image (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def comparedLinePullback (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Z : Scheme.{u}} (f : X ⟶ Z) (hZ : IsUnit (N : Γ(Z, ⊤))) :
    (comparison A X).obj ((Etale.ordinaryFinitePullback A f).obj
      ((Etale.ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧)) ≅
    (comparison A X).obj ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) :=
  (comparison A X).mapIso (Etale.ordinaryFiniteShiftedLinePullback A N hA
    (Etale.projectiveLineTraceTransport N hN A hA) f hZ)

/-- The ordinary tensor-source object, cached before scheme specialization.
Source: ordinary source display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def ordinarySourceObject (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (f : X ⟶ Z) (W : Etale.DerivedCategoryModule A X)
    (K : Etale.DerivedCategoryModule A Z) : Etale.DerivedCategoryModule A X :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((Etale.ordinaryFinitePullback A f).obj K)).obj W

/-- The literal tensor source of the compact-support projection.
Source: Pi_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def projectionSourceObject (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (f : X ⟶ Z)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj F

/-- The actual pro-etale tensor-source object, with compared coefficient.
Source: twisted source display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def proSourceObject (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (f : X ⟶ Z) (W : Etale.DerivedCategoryModule A X)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  projectionSourceObject A f ((comparison A X).obj W) K

/-- Canonical pullback/tensor comparison followed by an arbitrary realization isomorphism.
Source: the displayed ordinary source identification
(blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def realizedTensorComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (f : X ⟶ Z)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (Ke : Etale.DerivedCategoryModule A Z) (W : Etale.DerivedCategoryModule A X)
    (eK : (comparison A Z).obj Ke ≅ K) :
    (comparison A X).obj (ordinarySourceObject A f W Ke) ≅ proSourceObject A f W K := by
  unfold ordinarySourceObject proSourceObject projectionSourceObject
  exact tensorPullbackComparison A f Ke W ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.mapIso eK)).app _


/-- The coefficient right unitor with the literal compared ordinary coefficient unit.
Source: a_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def moduleRightUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj (unit A T) ≅ K :=
  coefficientRightUnit (ModuleCat.{u + 1} A) T K

/-- Tensor integration with the literal compared ordinary coefficient unit.
Source: a_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def moduleTensorTrace (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K Z W : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (e : Z ≅ ((derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj W)
    (t : W ⟶ unit A T) : Z ⟶ K :=
  e.hom ≫ ((derivedTensor (ModuleCat.{u + 1} A) T).obj K).map t ≫
    (moduleRightUnit A T K).hom

/-- The literal coefficient-first tensor target of inverse projection.
Source: Pi_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def projectionTargetObject (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :=
  ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).obj
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj F)

/-- Invertibility of the specified canonical coefficient-first projection map.
This is exactly IsIso of the symmetry-adjusted projection transformation.
Source: Pi_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def ProjectionInvertible (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) : Prop :=
  IsIso (projection (ModuleCat.{u + 1} A) c F K)

/-- The inverse of the actual symmetry-adjusted canonical compact-support projection.
Source: Pi_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def inverseProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (h : ProjectionInvertible A c F K) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (projectionSourceObject A f F K) ≅ projectionTargetObject A c F K := by
  unfold projectionSourceObject projectionTargetObject
  unfold ProjectionInvertible at h
  letI := h
  exact (asIso (projection (ModuleCat.{u + 1} A) c F K)).symm

/-- Inverse canonical projection, tensor integration and the literal coefficient unitor.
Source: a_K display (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def projectionTensorTrace (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} {f : X ⟶ Z} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (t : (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj F ⟶ unit A Z)
    (h : ProjectionInvertible A c F K) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
      (projectionSourceObject A f F K) ⟶ K := by
  let e := inverseProjection A c F K h
  unfold projectionTargetObject at e
  exact e.hom ≫ ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map t ≫
    (moduleRightUnit A Z K).hom


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The ordinary Ring structure is the one induced by the existing CommRing structure.
This cache aligns specialized ModuleCat coefficients with the generic canonical maps.
Source: coefficient convention (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
instance (priority := 2000) coefficientRing : Ring (Scheme.finiteTateCoefficient l E n) :=
  (inferInstance : CommRing (Scheme.finiteTateCoefficient l E n)).toRing

/-- Finiteness of the existing positive-level quotient coefficient ring.
Source: finite purity conventions (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
instance coefficientFinite : Finite (Scheme.finiteTateCoefficient l E n) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos _)
  exact inferInstanceAs (Finite (ULift.{u + 1}
    (Padic.coefficientExtensionRing l E (n + 1))))

variable (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)

/-- The canonical finite-Tate comparison for an arbitrary inverse image, including shift.
Its geometric specialization below is the chosen affine chart.
Source: Tate pullback and tau (blueprint: def-pur-affine-line-purity-coordinate-maps). -/
@[irreducible]
def twistPullbackComparison {X Z : Scheme.{u}} (f : X ⟶ Z)
    (hZ : IsUnit (l : Γ(Z, ⊤))) (hX : IsUnit (l : Γ(X, ⊤))) :
    (comparison (Scheme.finiteTateCoefficient l E n) X).obj
      ((Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n) f).obj
        ((Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA Z)⟦(2 : ℤ)⟧)) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteTateProSheaf l E n X 1))⟦(2 : ℤ)⟧ :=
  comparedLinePullback (Scheme.finiteTateCoefficient l E n)
    (l ^ (r + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA f
      (by simpa only [Nat.cast_pow] using hZ.pow (r + 1)) ≪≫
    twistDerived l E n X hX r hA 1 2


end AlgebraicGeometry.ProEtale.AffineLinePurity
