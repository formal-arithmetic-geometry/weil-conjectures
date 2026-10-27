/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.SecSmoothPurity.ReductionExceptionalObjects

/-! # Ordinary exceptional coefficient comparison on one coordinate chart

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts
(blueprint: lem-pur-ordinary-chart-exceptional-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The ordinary exceptional coefficient mate, restricted to one source chart, is
canonical scalar reassociation for the sum-then-ordered-affine right adjunction.
Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, chart argument, and
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, Proof (2).
(blueprint: lem-pur-ordinary-chart-exceptional-scalar).

Proof: transpose both sides under the B-coefficient chart adjunction. The definition
of reductionEtaleChartRightIso preserves the counit of the compactified exceptional
adjunction. The defining transpose equation for mateMap therefore expresses the
second path as scalar extension of the A-counit, preceded by the inverse compact
support comparison. For the first path, the graph normalization of MA and MB
identifies the etale part with summation on sheets. Scalar extension commutes with
this sum and its evaluation counit. On each ordered affine coordinate the normalized
P1 counit is the inverse of the two-summand Kummer decomposition followed by its
second projection. The Kummer boundary and the two summand maps commute with
coefficient extension: on roots the map is z tensor a tensor b to z tensor phi(a)b.
Consequently the inverse decomposition and its trace commute as well. Tensoring
this trace with the input, using the canonical tensorator and pullback balancing,
proves the affine counit square. Paste these squares in coordinate order, then
with the etale sum square; naturality moves the intermediate counits past each
comparison. The two transposes are now identical. Injectivity of the chart
adjunction bijection proves the equation. This is entirely on the ordinary etale
site and needs no presentation over a field. Rank-one Tate lines are flat over A,
so no flatness of B over A is used. For dimension zero the affine adjunction is
identity; for zero coefficient rings every object and map is zero. No covering
or isomorphism detection is part of this local assertion. -/
theorem ordinary_chart_exceptional_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {V S U : Scheme.{u}} [IsNoetherian V] [IsNoetherian S] [IsNoetherian U]
    (hS : IsUnit (N : Γ(S, ⊤))) (g : V ⟶ S) [HasCompactification g]
    (i : U ⟶ V) [IsOpenImmersion i] (d : ℕ)
    (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (he : i ≫ g = e ≫ affineTraceProjection S d)
    (MA : EtaleCompactSupportNormalization A) (MB : EtaleCompactSupportNormalization B)
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA tA T hT)
    (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum B N hB tB T hT)
    (K : DerivedCategoryModule A S) :
    (scalarExtension φ U).map
        ((ProEtale.reductionEtaleChartRightIso A MA g i d e he
          (HasCompactification.compactification g)
          (rightDerivedUpperShriek (ModuleCat.{u + 1} A) g)
          (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) g)
          N hA tA PA hS).hom.app K) ≫
      (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e K).hom =
    (scalarPullbackIso φ i).inv.app
        ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) g).obj K) ≫
      (ordinaryFinitePullback B i).map (ExceptionalCoefficients.mateMap φ g K) ≫
      (ProEtale.reductionEtaleChartRightIso B MB g i d e he
        (HasCompactification.compactification g)
        (rightDerivedUpperShriek (ModuleCat.{u + 1} B) g)
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) g)
        N hB tB PB hS).hom.app ((scalarExtension φ S).obj K) := by sorry

end AlgebraicGeometry.Etale
