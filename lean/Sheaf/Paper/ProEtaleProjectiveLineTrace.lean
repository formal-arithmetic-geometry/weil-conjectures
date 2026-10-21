module

public import Sheaf.Paper.SupportedProjectiveChern

/-! # Supported projective-line site arrows
Source: supported Cartier Kummer map and projective-line normalization
(blueprint: def-pur-supported-projective-site-arrows).
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

/-- The pro-etale decomposition has exactly the two specified components.
Source: projective-line normalization
(blueprint: def-pur-supported-projective-site-arrows). -/
@[irreducible]
def projectiveB (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤)))
    (hI : (ProjectiveLine.infinity S).ker.IsInvertible) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (line l E n r hA S ⊞ unit (Scheme.finiteTateCoefficient l E n) S) ⟶
      (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj (line l E n r hA
          (ProjectiveLine S)) :=
  biprod.desc (projectiveU l E n S hS r hA) (projectiveH l E n S hS hI r hA)


/-- Bounded-below realization of the shifted ordinary Tate line.
Source: degree-zero complexes and shifts
(blueprint: def-pur-supported-projective-site-arrows). -/
abbrev linePlus (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))) :=
  ⟨(Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA T)
      ⟦(2 : ℤ)⟧, ⟨-2, DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)⟩⟩

/-- The finite-sum identification is induced by the two projections, with no new scalar.
Source: additivity of exact comparison
(blueprint: def-pur-supported-projective-site-arrows). -/
@[irreducible]
def projectiveSum (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (S : Scheme.{u}) :=
  biprod.lift
    ((comparison (Scheme.finiteTateCoefficient l E n) S).map
      (biprod.fst (X := (Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
        (l ^ (r + 1)) hA S)⟦(2 : ℤ)⟧)
        (Y := Etale.ordinaryFiniteUnit (Scheme.finiteTateCoefficient l E n) S)))
    ((comparison (Scheme.finiteTateCoefficient l E n) S).map biprod.snd)

/-- Invertibility of the two-component pro-etale decomposition.
Source: projective-line decomposition and supported Kummer normalization
(blueprint: def-pur-supported-projective-site-arrows).
Proof: the canonical direct-image mate carries the ordinary unit and Chern components
to these components, by the mate's counit equation and the supported Kummer comparison.
Comparison preserves biproducts, so it carries the ordinary decomposition to this map.
The ordinary decomposition and both boundary comparisons are invertible.
-/
theorem projectiveB_isIso (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    IsIso (projectiveB l E n S hS hI r hA) := by
  sorry

/-- Projection onto the second summand after the actual pro-etale decomposition.
Source: def-amb-p1-trace (blueprint: def-pur-supported-projective-site-arrows). -/
@[irreducible]
def projectiveTrace (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine S ↘ S)).rightDerivedFunctor.obj
        (line l E n r hA (ProjectiveLine S)) ⟶ unit (Scheme.finiteTateCoefficient l E n) S :=
  letI := projectiveB_isIso l E n S hS hI r hA
  geoP1Trace (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hA S
    (asIso (projectiveB l E n S hS hI r hA))


end AlgebraicGeometry.ProEtale.VectorIntegrationSite
