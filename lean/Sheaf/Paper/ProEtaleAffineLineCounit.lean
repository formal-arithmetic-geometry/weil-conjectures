module

public import Sheaf.Paper.ProEtaleProjectionIntegration

/-! # Canonical pro-etale ordered integration arrows
Source: main-20261015 vector-bundle integration and projective-line normalization
(blueprint: def-pur-proetale-affine-line-counit).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)


/-- The exact derived open adjunction, in left-derived inverse-image coordinates.
Source: Stacks 09AF (blueprint: def-pur-proetale-affine-line-counit). -/
@[irreducible]
def openAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm

/-- One actual open/proper left functor of the ordered pro-etale tower.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-affine-line-counit). -/
abbrev lineLeft (T : Scheme.{u}) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (ProjectiveLine.affineChart T)).mapDerivedCategory ⋙
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine T ↘ T)).rightDerivedFunctor

/-- The type of the canonical affine-line right-object comparison.
Source: Stacks 099R (blueprint: def-pur-proetale-affine-line-counit). -/
@[implicit_reducible]
def LineRightComparisonIso (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :=
  (comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} T)).obj
    ((Etale.affineTraceLineRight _ (l ^ (r + 1)) hA T).obj K) ≅
  (upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (ProjectiveLine.affineChart T)).leftDerivedFunctor.obj
      (projectiveRight l E n r hA T K)

/-- Comparison of the right affine-line coefficient, using pullback and tensor only.
Source: Stacks 099R (blueprint: def-pur-proetale-affine-line-counit). -/
@[irreducible]
def lineRightComparison (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :
    LineRightComparisonIso l E n r hA T K :=
  pullbackThen (Scheme.finiteTateCoefficient l E n) (ProjectiveLine.affineChart T)
    _ _ (projectiveRightComparison l E n r hA T K)

/-- Restrict the independent projective counit by the actual extension-by-zero counit.
Source: blueprint affine-line trace (blueprint: def-pur-proetale-affine-line-counit). -/
@[irreducible]
def lineCounit (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (hI : (ProjectiveLine.infinity T).ker.IsInvertible)
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    (lineLeft (Scheme.finiteTateCoefficient l E n) T).obj
      ((comparison (Scheme.finiteTateCoefficient l E n) (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.affineTraceLineRight _ (l ^ (r + 1)) hA T).obj K.obj)) ⟶
      (comparison (Scheme.finiteTateCoefficient l E n) T).obj K.obj :=
  (lineLeft (Scheme.finiteTateCoefficient l E n) T).map
      (lineRightComparison l E n r hA T K.obj).hom ≫
    (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine T ↘ T)).rightDerivedFunctor.map
        ((openAdjunction (Scheme.finiteTateCoefficient l E n)
          (ProjectiveLine.affineChart T)).counit.app (projectiveRight l E n r hA T K.obj)) ≫
    projectiveEpsilon l E n T hT hI r hA K

/-- The infinity section is the relative effective Cartier hyperplane.
Source: projective-line standard charts
(blueprint: def-pur-proetale-affine-line-counit).
Proof: on the chart containing infinity its ideal is the polynomial coordinate,
which is a non-zero-divisor over any base ring; on the other chart it is the unit
ideal. These invertible ideals glue. This includes the empty base.
-/
theorem infinityCartier (T : Scheme.{u}) :
    (ProjectiveLine.infinity T).ker.IsInvertible := by
  sorry


end AlgebraicGeometry.ProEtale.VectorIntegrationSite
