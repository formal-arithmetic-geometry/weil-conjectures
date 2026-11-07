/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference

import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstAmbientContraction
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondAmbientContraction

/-! # Ambient rational projective-line kernel contractions

This is the geometric calculation preceding integration in the rational
projective-line triangle argument. It uses normalization by the explicit
diagonal-class and trace pastes, and asserts the kernel formulas before integration.
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

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] coefficient line diagram secondLineComparison

-- The canonical ambient pastes use the existing unit/counit elaboration allowance.
/-- The ambient diagonal-class insertion and trace contraction give the two kernel
integrals. This statement concerns the ambient pastes for any pair of natural transformations
whose components have the specified canonical normalization. No adjunction is assumed.
Source: blueprint triangle identities, proof steps 1--4
(blueprint: lem-rational-p1-kernel-contractions).
Proof:
Write P = P¹_Y, W = P ×_Y P, R = Rq_*, A = p₁*, B = p₂*, S = Rp₁*, U = Rp₂*,
and T for the shifted Tate line. All functors and comparisons below are the canonical
ones used in `unitComponent` and `counitComponent`.

1. The module/ringed-topos comparison preserves adjunctions, tensors, their projection
mates, and composition comparisons. The proper localizing projection formula and proper
base change invert exactly the arrows in the two ambient pastes. Cancel the native
`tensorShiftIso` and its inverse; this puts the pastes into tensor-by-T notation.
The unit is the canonical section M → UΔ_*M, followed by U of the diagonal-class map,
followed by b_M⁻¹, where b_M is exchange followed by the p₂ projection formula.
The counit is the inverse q projection formula followed by identity tensor Tr_q.

2. The two Kunneth factorizations give the same map
R M ⊗ R T → RU(A M ⊗ T_W) = RS(A M ⊗ T_W).
They have equal transposes under the original composite pullback/direct-image
adjunctions. Insert its first factorization in R(unitComponent) followed by the counit,
and rewrite using its second factorization. Transport the trace comparison of the
referenced completed family through its scalar-compatibility squares. Base change
identifies the resulting pullback of Tr_q with Tr_p₁. Projection naturality moves the
class through the p₁ projection formula, leaving R of identity tensor the p₁ integral.

3. For M = q* K ⊗ T_P, use q p₁ = q p₂ and the normalized Cartesian Tate comparisons
to identify A M with B M. The projection/exchange tensor square rewrites b_M⁻¹ followed
by q*(counitComponent) tensor identity as the inverse p₂ projection formula followed
by identity tensor Tr_p₂. Here the p₂ trace is again the transported base change of
Tr_q. Tensor-associativity coherence keeps the outside Tate factor in the indicated
position. The symmetry on the two Tate factors is the identity: the degree-zero
rank-one line has trivial self-symmetry and both shifts have degree two.

4. For each i, the projection map for Δ and the section comparison have identity
transpose under Δ* p_i* = identity. Consequently the inverse diagonal tensor map is
the canonical section normalization. For i = 2 the same statement also identifies
the p₁ and p₂ presentations of that map on q* K ⊗ T_P. The projection/composition
section identity therefore turns the source of the remaining tensor map into the
right-unitor source. Naturality in the class makes the interior arrow precisely
support_i.hom followed by R_i(delta) and trace_i. The full universal-unit and
supported-source normalizations in Diagram identify these arrows with the literal
ones below, including singleUnitIso on both sides. No integration identity is used. -/
theorem rationalP1_kernel_contractions
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (_hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (_hsystem : DiagonalCycleSystemSpec l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (_hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (family : Family l Y) (_reference : Reference l Y δ family)
    (a : UnitCounitType l c k p hpl Y)
    (_hnorm : UnitCounitNormalized l c k p hpl Y family a) :
    (∀ M : rationalLocalizingCategory (coefficient l c).X (ProjectiveLine Y),
      ((push l c k p hpl Y).map (a.1.app M) ≫
        a.2.app ((push l c k p hpl Y).obj M)).hom =
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (((ρ_ (M.obj)).inv ≫ ((M.obj) ◁
          ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
            (diagram l c Y family).support₁.hom ≫
            (diagram l c Y family).R₁.R.map (diagram l c Y family).delta ≫
            (diagram l c Y family).trace₁ ≫
            (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom)) ≫ (ρ_ (M.obj)).hom))) ∧
    (∀ K : rationalLocalizingCategory (coefficient l c).X Y,
      (a.1.app ((exceptional l c k p hpl Y).obj K) ≫
        (exceptional l c k p hpl Y).map (a.2.app K)).hom =
      (ρ_ (((exceptional l c k p hpl Y).obj K).obj)).inv ≫
        ((((exceptional l c k p hpl Y).obj K).obj) ◁
          ((singleUnitIso (coefficient l c).X (ProjectiveLine Y)).inv ≫
            (diagram l c Y family).support₂.hom ≫
            (diagram l c Y family).R₂.R.map (diagram l c Y family).delta ≫
            (diagram l c Y family).trace₂ ≫
            (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom)) ≫
        (ρ_ (((exceptional l c k p hpl Y).obj K).obj)).hom) := by
  constructor
  · intro M
    change ((moduleObjectDerivedPushforward (coefficient l c).X
      (ProjectiveLine Y ↘ Y)).map (a.1.app M).hom ≫
        (a.2.app ((push l c k p hpl Y).obj M)).hom :
        (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M.obj ⟶
          (moduleObjectDerivedPushforward (coefficient l c).X
            (ProjectiveLine Y ↘ Y)).obj M.obj) = _
    exact rationalP1_first_ambient_contraction l c k p hpl Y δ family _reference
        M.obj M.property (a.1.app M).hom
        (a.2.app ((push l c k p hpl Y).obj M)).hom
        (_hnorm.1 M) (_hnorm.2 ((push l c k p hpl Y).obj M))
  · intro K
    change ((a.1.app ((exceptional l c k p hpl Y).obj K)).hom ≫
      (twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).map
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
          (a.2.app K).hom) :
        ((exceptional l c k p hpl Y).obj K).obj ⟶
          ((exceptional l c k p hpl Y).obj K).obj) = _
    exact rationalP1_second_ambient_contraction l c k p hpl Y δ family _reference
      K.obj K.property (a.1.app ((exceptional l c k p hpl Y).obj K)).hom
      (a.2.app K).hom (_hnorm.1 ((exceptional l c k p hpl Y).obj K)) (_hnorm.2 K)

end AlgebraicGeometry.ProEtale.RationalP1
