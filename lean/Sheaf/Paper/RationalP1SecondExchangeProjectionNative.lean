/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.Paper.RationalP1SecondPretraceData

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] secondLineComparison twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange


/-- The native exchange component with its module-object endpoints exposed. -/
def nativeExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) ⟶
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M) := by
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact (condensedAmbientExchange Λ (square Y)).app M

/-- The forward exchange/projection square, before adding an outside Tate factor.
There is no inverse projection, twisted projection, or invertibility assumption.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, extraction of q*K; ringed exchange/tensor coherence.
(blueprint: lem-sfb-rational-p1-second-exchange-projection-native).

Proof: apply the exchange/tensor square with inside T=L_P[2] and outside K.
Transport its tensor, projection and exchange arrows through the internal-module/ringed
comparison, including its canonical adjunction and composition clauses. Change from
right-factor to left-factor projection with the native Koszul symmetries. Naturality
of exchange for tensorShiftIso.hom changes the exchanged object from q*K tensor T to
its specified twist. Apply the first root-normalized pulled-line comparison and the
self-square pullback comparison on K. The target comparison is exactly the inverse
of pullTwistIso in secondExtractProjection. Naturality of projection moves the line
comparison onto the scalar exchange. The tensor comparison at q is the inverse of
the canonical monoidal tensorator. This gives the displayed forward square for every
K; neither an exchange nor a projection is inverted. -/
theorem second_exchange_projection_native
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    let Λ := (coefficient l c).X
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
    F.map (projectionMap Λ (ProjectiveLine Y ↘ Y) K T) ≫
        F.map (R.map (tensorShiftIso Λ (ProjectiveLine Y)
          (line l c (ProjectiveLine Y)) (F.obj K)).hom) ≫
        nativeExchange Λ Y
          ((twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj (F.obj K)) =
      (secondTraceTensorIso Λ Y K (R.obj T)).inv ≫
        (F.obj K ◁ secondTraceExchange l c k p hpl Y) ≫
        secondExtractProjection l c k p hpl Y K := by sorry

end AlgebraicGeometry.ProEtale.RationalP1
