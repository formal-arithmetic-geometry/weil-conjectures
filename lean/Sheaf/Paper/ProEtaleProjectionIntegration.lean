module

public import Sheaf.Paper.ProEtaleProjectiveCoefficient

/-! # Canonical pro-etale ordered integration arrows
Source: main-20261015 vector-bundle integration and projective-line normalization
(blueprint: def-pur-proetale-projection-integration).
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

set_option linter.unusedVariables false in
/-- Invertibility of the specified proper projection on bounded etale-origin inputs.
Source: Stacks 0GL1; Step 7 of the node
(blueprint: def-pur-proetale-projection-integration).
Proof: tensor the ordinary projection comparison square with the two canonical site
comparisons. The Tate line is locally free, so the proper projection theorem applies
without flatness of the coefficient ring over the Kummer ring. All four boundary
comparisons and the ordinary projection are invertible, hence so is this map.
-/
theorem projectiveProjection_isIso (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤)))
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    IsIso (properProjection (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ProjectiveLine T ↘ T)
      (line l E n r hA (ProjectiveLine T))
      ((comparison (Scheme.finiteTateCoefficient l E n) T).obj K.obj)) := by
  sorry

/-- The Hom type of the projective counit, using the canonical tensor source.
Source: Stacks 0GL1 (blueprint: def-pur-proetale-projection-integration). -/
@[implicit_reducible]
def ProjectiveEpsilonHom (T : Scheme.{u})
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :=
  ProperIntegrationHom (Scheme.finiteTateCoefficient l E n) (ProjectiveLine T ↘ T)
    (line l E n r hA (ProjectiveLine T)) K

/-- The counit is uniquely determined by the actual proper projection and trace.
Source: Stacks 0GL1 (blueprint: def-pur-proetale-projection-integration).
Proof: the projection is invertible by projectiveProjection_isIso. Compose its
inverse with tensor of the supported trace and the right unitor. Cancellation
with the projection proves uniqueness.
-/
theorem existsUniqueProjectiveEpsilon (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (hI : (ProjectiveLine.infinity T).ker.IsInvertible)
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    ∃! e : ProjectiveEpsilonHom l E n T r hA K.obj,
      ProperIntegrationEquation (Scheme.finiteTateCoefficient l E n) (ProjectiveLine T ↘ T)
        (line l E n r hA (ProjectiveLine T)) K.obj (projectiveTrace l E n T hT hI r hA) e := by
  sorry

/-- The unique counit determined by the actual proper projection and trace.
Source: Stacks 0GL1 (blueprint: def-pur-proetale-projection-integration). -/
@[irreducible]
def projectiveEpsilon (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (hI : (ProjectiveLine.infinity T).ker.IsInvertible)
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    ProjectiveEpsilonHom l E n T r hA K.obj :=
  (existsUniqueProjectiveEpsilon l E n T hT hI r hA K).exists.choose

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
