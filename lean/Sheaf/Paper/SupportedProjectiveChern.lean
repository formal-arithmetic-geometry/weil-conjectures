module

public import Sheaf.Paper.FiniteSiteCoordinates
public import Sheaf.AlgebraicGeometry.CartierKummerMap

/-! # Supported projective-line site arrows
Source: supported Cartier Kummer map and projective-line normalization
(blueprint: def-pur-supported-projective-chern).
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

/-- The supported pro-etale Chern arrow, expressed with its specified source and target
comparisons. Its middle map is the actual Cartier Kummer morphism, independently of the
ordinary projective-line decomposition.
Source: Cartier Kummer map; Stacks 099R
(blueprint: def-pur-supported-projective-chern). -/
@[irreducible]
def projectiveChern (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤)))
    (hI : (ProjectiveLine.infinity S).ker.IsInvertible) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    unit (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S) ⟶ line l E n r hA
      (ProjectiveLine S) :=
  ((comparisonUpperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (ProjectiveLine S)).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map
      (Etale.cartierConstantComparison (Scheme.finiteTateCoefficient l E n)
        (ProjectiveLine S) ≫ Etale.cartierSupportedUnit l E n (ProjectiveLine.infinity S)) ≫
    Etale.cartierKummerMap l E n (ProjectiveLine.infinity S) hI
      (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom) ≫
    (twistDerived l E n (ProjectiveLine S)
      (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom) r hA 1 2).inv

/-- The adjoint of the supported pro-etale Chern arrow, with the canonical constant unit.
Source: projective-line normalization
(blueprint: def-pur-supported-projective-chern). -/
@[irreducible]
def projectiveH (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤)))
    (hI : (ProjectiveLine.infinity S).ker.IsInvertible) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    unit (Scheme.finiteTateCoefficient l E n) S ⟶
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj (line l E n r hA
          (ProjectiveLine S)) :=
  (derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (ProjectiveLine S ↘ S)).homEquiv _ _
      ((pullbackUnit (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)).hom ≫
        projectiveChern l E n S hS hI r hA)

/-- The shifted twisted unit, independently formed from the pro-etale adjunction.
Source: projective-line normalization
(blueprint: def-pur-supported-projective-chern). -/
@[irreducible]
def projectiveU (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    line l E n r hA S ⟶
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj (line l E n r hA
          (ProjectiveLine S)) :=
  (derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
    (ProjectiveLine S ↘ S)).homEquiv _ _
      ((pullback (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)).inv.app _ ≫
        (comparison (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S)).map
          (Etale.ordinaryFiniteShiftedLinePullback (Scheme.finiteTateCoefficient l E n)
            (l ^ (r + 1)) hA
            (Etale.projectiveLineTraceTransport (l ^ (r + 1))
              (pow_pos (Fact.out : l.Prime).pos _) _ hA)
            (ProjectiveLine S ↘ S) (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).hom)

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
