/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference

import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTraceTransport
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitFactorization

/-! # First ambient projective-line contraction

Source: the first and second kernel calculations in the rational projective-line
triangle proof, before integration.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] coefficient line diagram secondLineComparison
attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] twist projectionMap singleUnitIso
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] condensedAmbientExchange

-- Keep the fixed geometric coefficient and derived interfaces folded during elaboration.
/-- The first kernel calculation at a single localizing object, for two arrows
normalized by the literal ambient formulas. No natural transformation or adjunction for the twisted
functor is assumed.
No integration identity is used. The completed class need not be a limit class for this calculation.

Source: current blueprint, sec-six-functors-basics/sk-prop-p1-adjunction-rational/
sk-prop-p1-adjunction-rational-triangle.proof.md, First identity
(blueprint: lem-sfb-rational-p1-first-ambient-contraction).

Proof: Open the two normalization predicates and rewrite their HEq witnesses. The
existential witnesses select only proofs of invertibility of fixed arrows. Put P = P¹_Y, W = P ×_Y
P, R = Rq_*, A = p₁*, B = p₂*,
S = Rp₁*, U = Rp₂*, and T_Z = L_Z[2]. Transport the canonical projection and exchange
maps through the module/ringed-topos comparison, preserving their adjoint transposes.
Cancel the tensorShiftIso factors in the unit and counit. The unit is the section map
M → UΔ_*M, followed by U of the diagonal tensor isomorphism and the class, then the
inverse of b_M: q*RM ⊗ T_P → U(AM ⊗ T_W). The counit is the inverse q projection
followed by identity tensor Tr_q. Properness and the localizing projection formula
make the remaining projection factors invertible.

The two Kunneth factorizations, with second factor T_P, identify R(b_M) with the
alternative factorization through S and the base-changed trace. Reference identifies
the completed traces with family.zl, and the scalar squares in Family transport this
equality to the selected rational or closure coefficient. The canonical base-change
trace square identifies q*Tr_q with Tr_p₁ after exchange. Projection naturality then
moves M outside S and moves the class through that projection. The inverse diagonal
tensor map has identity adjoint transpose under Δ*p₁* = identity, so the projection
section identity identifies its source with the coefficient right unitor on M.
The full-unit normalizations of the selected diagram and its source identify the remaining
arrow with support₁.hom ≫ R₁(delta) ≫ trace₁. Conjugating by singleUnitIso gives the
stated literal endomorphism. No assertion that this integral equals identity is used. -/
theorem rationalP1_first_ambient_contraction
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (_reference : Reference l Y δ family)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (_hM : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y)) M)
    (η : M ⟶ (twist (coefficient l c).X (ProjectiveLine Y)
      (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)))
    (ε : (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward (coefficient l c).X
            (ProjectiveLine Y ↘ Y)).obj M))) ⟶
        (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)
    (_hη : UnitComponentNormalized (coefficient l c).X Y (line l c) (diagram l c Y family)
      (secondLineComparison l c k p hpl Y) M η)
    (_hε : CounitComponentNormalized (coefficient l c).X Y (line l c)
      (diagram l c Y family)
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M) ε) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map η ≫ ε =
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        ((ρ_ M).inv ≫ (M ◁
          ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
            (diagram l c Y family).support₁.hom ≫
            (diagram l c Y family).R₁.R.map (diagram l c Y family).delta ≫
            (diagram l c Y family).trace₁ ≫
            (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom)) ≫ (ρ_ M).hom) := by
  obtain ⟨hb, hp, hunit⟩ := rationalP1_unit_factorization l c k p hpl Y family M η _hη
  have htrace := rationalP1_first_trace_transport l c k p hpl Y δ family _reference
    M _hM ε _hε hb hp
  have h₁ := Classical.choose htrace
  have ht := Classical.choose_spec htrace
  let R := moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)
  let U := moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)
  let A := moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)
  let N : DerivedCategory (Modules (coefficient l c).X (diagonalSurface Y)) :=
    ((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
      (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧
  let a := firstKernelInsertion (coefficient l c).X Y M N (diagram l c Y family).delta
  let v : U.obj (A.obj M ⊗ N) ⟶
      (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          (R.obj M)) :=
    U.map (X := A.obj M ⊗ N)
        (tensorShiftIso (coefficient l c).X (diagonalSurface Y)
          (line l c (diagonalSurface Y)) (A.obj M)).hom ≫
      @inv _ _ _ _ (twistProjectionMap (coefficient l c).X (secondProjection Y)
        (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
        (secondLineComparison l c k p hpl Y) (A.obj M)) hp ≫
      (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map
        (by
          dsimp only [R, U, A]
          unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
          exact @inv _ _ _ _
            ((condensedAmbientExchange (coefficient l c).X (square Y)).app M) hb)
  have hu : η = a ≫ v := by
    simpa only [R, U, A, N, a, v, id] using
      hunit
  have ht' : R.map v ≫ ε =
      firstTerminalFunctional (coefficient l c).X Y (line l c) (diagram l c Y family)
        M N (diagram l c Y family).trace₁ h₁ := by
    simpa only [R, U, A, N, v, id] using ht
  calc
    R.map η ≫ ε = R.map (a ≫ v) ≫ ε := by rw [hu]
    _ = R.map a ≫ (R.map v ≫ ε) := by rw [Functor.map_comp, Category.assoc]
    _ = R.map a ≫ firstTerminalFunctional (coefficient l c).X Y (line l c)
        (diagram l c Y family) M N (diagram l c Y family).trace₁ h₁ :=
      congrArg (fun f => R.map a ≫ f) ht'
    _ = _ := first_section_tensor_evaluation l c Y (line l c) (diagram l c Y family)
      M N (diagram l c Y family).delta (diagram l c Y family).trace₁ h₁

end AlgebraicGeometry.ProEtale.RationalP1
