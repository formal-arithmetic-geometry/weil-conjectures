/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.Paper.RationalP1SecondPretraceData

/-! The generic strength/projection interchange used by the rational P1 calculation.

This isolates the monoidal coherence calculation from the fixed projective-line
projection maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] secondLineComparison twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- The strength tail with an arbitrary second tensor factor. It is the
monoidal tensor/shift coherence after the first factor has been shifted. -/
@[irreducible]
def secondTraceStrengthTail
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : Modules Λ (ProjectiveLine Y))
    (K : DerivedCategory (Modules Λ Y))
    (Q : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (twist Λ (ProjectiveLine Y) L).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ⊗ Q ⟶
      (twist Λ (ProjectiveLine Y) L).obj
        (((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ⊗ Q) := by
  letI := secondTraceBraided Λ Y
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj L)
    ⟦(2 : ℤ)⟧
  exact
    (tensorShiftIso Λ (ProjectiveLine Y) L (F.obj K)).inv ▷ Q ≫
      (α_ (F.obj K) T Q).hom ≫
      (tensorIso (Iso.refl _) (β_ T Q)).hom ≫
      (α_ (F.obj K) Q T).inv ≫
      (tensorShiftIso Λ (ProjectiveLine Y) L (F.obj K ⊗ Q)).hom

/-- Monoidal strength naturality for an arbitrary morphism in the second factor.
The statement is independent of the projective-line projection and is the
coherence calculation needed before inserting the fixed projection maps.
Source: the second identity of the rational projective-line triangle calculation.
(blueprint: lem-sfb-rational-p1-second-projection-interchange). -/
theorem secondTraceStrength_naturality
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K V : DerivedCategory (Modules (coefficient l c).X Y))
    (Q R Z : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (z : (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj V ⟶ Q)
    (q : ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K) ⊗ Q ⟶ R)
    (τ : (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj R ⟶ Z) :
    (secondTraceStrength (coefficient l c).X Y (line l c (ProjectiveLine Y)) K V).hom ≫
        (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map
          ((secondTraceTensorIso (coefficient l c).X Y K V).inv ≫
            ((moduleObjectDerivedPullback (coefficient l c).X
              (ProjectiveLine Y ↘ Y)).obj K ◁ z) ≫ q) ≫ τ =
      (((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) ◁ z) ≫
        secondTraceStrengthTail (coefficient l c).X Y (line l c (ProjectiveLine Y)) K Q ≫
        (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map q ≫ τ := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
