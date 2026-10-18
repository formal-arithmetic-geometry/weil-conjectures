module


public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.RingTheory.ExcellentRing
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Sheaf.AlgebraicGeometry.GenericSmoothBoundaryPreparation
import Sheaf.AlgebraicGeometry.RelativeCurveFactorization
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Preparation of an alteration problem as a relative curve

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé X, proof of Theorem 3.5,
Steps 2 and 5 (blueprint: lem-trf-alteration-relative-curve-preparation).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

@[expose] public section

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé X, proof of Theorem 3.5,
Steps 2 and 5 (blueprint: lem-trf-alteration-relative-curve-preparation).
The proof first applies `lem-trf-relative-curve-factorization` to obtain an excellent
relative-curve factorization. It then applies `lem-trf-generic-smooth-boundary-preparation`
to make the generic fibre smooth and the reduced inverse boundary finite étale. Finally,
projectivity gives properness and the finite generic-field extension preserves the fibre
dimension, using `lem-pc-projective-proper` and
`lem-sc-closed-irreducible-dimension-trdeg`; these are exactly the three proof steps
recorded in the DAG. The field alternative is stated as `IsField A`, so it refers to
the given commutative-ring structure on the base rather than an unrelated field instance. -/
theorem alteration_relative_curve_preparation
    (A : Type u) [CommRing A]
    (hbase : IsField A ∨
      ∃ hD : IsDomain A,
        Nonempty (@IsDiscreteValuationRing A inferInstance hD) ∧ IsExcellent A)
    (S : Scheme.{u}) (eS : S = Spec (.of A)) (s : S)
    (hs : IsGenericPoint s Set.univ)
    (X : Scheme.{u}) (p : X ⟶ S) [IsIntegral X]
    (hp : IsProper p) (hdom : DenseRange p.base)
    (hft : LocallyOfFiniteType p ∧ QuasiCompact p)
    (d : ℕ) (hd : topologicalKrullDim (p.fiber s) = (d : WithBot ℕ∞))
    (hdpos : 1 ≤ d)
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : ∀ ξ : X, IsGenericPoint ξ Set.univ → ξ ∉ Set.range i.base) :
    ∃ (X₁ Y : Scheme.{u}) (h : X₁ ⟶ X) (q : Y ⟶ S) (f : X₁ ⟶ Y),
      IsIntegral X₁ ∧
      (∀ U : X₁.Opens, IsAffineOpen U → IsExcellent Γ(X₁, U)) ∧
      IsIntegral Y ∧
      (∀ U : Y.Opens, IsAffineOpen U → IsExcellent Γ(Y, U)) ∧
      IsProper h ∧ DenseRange h.base ∧
      (∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (h ∣_ U)) ∧
      IsHProjective q ∧ IsProper q ∧ DenseRange q.base ∧
      (LocallyOfFiniteType q ∧ QuasiCompact q) ∧
      topologicalKrullDim (q.fiber s) = ((d - 1 : ℕ) : WithBot ℕ∞) ∧
      IsProper f ∧ DenseRange f.base ∧
      h ≫ p = f ≫ q ∧
      (∀ y : Y, IsGenericPoint y Set.univ →
        SmoothOfRelativeDimension 1 (f.fiberToSpecResidueField y) ∧
        IsIntegral (f.fiber y) ∧
        IsFinite
          (((((Limits.pullback h i).nilradical.subschemeι ≫
            Limits.pullback.fst h i) ≫ f).fiberToSpecResidueField y)) ∧
        Etale
          (((((Limits.pullback h i).nilradical.subschemeι ≫
            Limits.pullback.fst h i) ≫ f).fiberToSpecResidueField y))) := by
  sorry

end AlgebraicGeometry

end
