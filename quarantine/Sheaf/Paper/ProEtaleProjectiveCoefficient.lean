module

public import Sheaf.Paper.FiniteSiteTensorProjection

/-! # Canonical pro-etale ordered integration arrows
Source: main-20261015 vector-bundle integration and projective-line normalization
(blueprint: def-pur-proetale-projective-coefficient).
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

/-- The projective right object before the coefficient ring is specialized.
Source: Stacks 0GL1 (blueprint: def-pur-proetale-projective-coefficient). -/
@[implicit_reducible]
def projectiveRightGeneric (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine T)) (ModuleCat.{u + 1} A)) :=
  ((derivedTensor (ModuleCat.{u + 1} A) (ProjectiveLine T)).obj
    ((upperStar (ModuleCat.{u + 1} A) (ProjectiveLine T ↘ T)).leftDerivedFunctor.obj
      ((comparison A T).obj K))).obj
    ((comparison A (ProjectiveLine T)).obj
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧))

/-- Canonical tensor/pullback comparison with the published ordinary right functor.
Source: Stacks 099R (blueprint: def-pur-proetale-projective-coefficient). -/
@[irreducible]
def projectiveRightComparisonGeneric (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T) :
    (comparison A (ProjectiveLine T)).obj ((Etale.ordinaryFiniteP1Right A N hA T).obj K) ≅
      projectiveRightGeneric A N hA T K :=
  tensorPullbackComparison A (ProjectiveLine T ↘ T) K
    ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧)

/-- The right-hand projective-line coefficient on the pro-etale site.
Source: projective-line trace (blueprint: def-pur-proetale-projective-coefficient). -/
abbrev projectiveRight (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :=
  projectiveRightGeneric (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA T K

/-- Canonical source comparison specialized to the fixed finite quotient.
Source: Stacks 099R (blueprint: def-pur-proetale-projective-coefficient). -/
@[irreducible]
def projectiveRightComparison (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :
    (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine T)).obj
      ((Etale.ordinaryFiniteP1Right _ (l ^ (r + 1)) hA T).obj K) ≅
        projectiveRight l E n r hA T K :=
  projectiveRightComparisonGeneric (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA T K

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
