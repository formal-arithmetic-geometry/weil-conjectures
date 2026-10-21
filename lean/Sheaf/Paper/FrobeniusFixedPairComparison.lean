/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.FdCoefficientComparisonSystem
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.FdCoefficientComparison
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Equivalence

/-! # Frobenius fixed-pair comparison for a supplied comparison system

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence, geometric-fibre and fixed-pair auxiliary
(blueprint: lem-fd-frobenius-fixed-pair-comparison).

The finite/common-stage transports and scalar/inclusion comparisons below use the
specified comparisons of the supplied system, with their recorded reverse orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (S : FdCoefficientComparisonSystem.{u} l Ω)
  (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (g : T ≅ T)

/-- A square of fixed-pair transports commutes by the specified coefficient comparison.
The component equality ensures that this is the supplied comparison, not an arbitrary
isomorphism of functors.
Source: trace-definition final sentence, auxiliary proof steps 8--10
(blueprint: lem-fd-frobenius-fixed-pair-comparison). -/
def FdFixedPairSquare
    {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ C₁} {F₂ : C₂ ⥤ C₂} {F₃ : C₃ ⥤ C₃} {F₄ : C₄ ⥤ C₄}
    {L₁₂ : C₁ ⥤ C₂} {L₂₄ : C₂ ⥤ C₄} {L₁₃ : C₁ ⥤ C₃} {L₃₄ : C₃ ⥤ C₄}
    (e₁₂ : L₁₂ ⋙ F₂ ≅ F₁ ⋙ L₁₂) (e₂₄ : L₂₄ ⋙ F₄ ≅ F₂ ⋙ L₂₄)
    (e₁₃ : L₁₃ ⋙ F₃ ≅ F₁ ⋙ L₁₃) (e₃₄ : L₃₄ ⋙ F₄ ≅ F₃ ⋙ L₃₄)
    (a : L₁₂ ⋙ L₂₄ ≅ L₁₃ ⋙ L₃₄) : Prop :=
  ∃ j : IsoAlgebra.mapOfNatIso e₁₂ ⋙ IsoAlgebra.mapOfNatIso e₂₄ ≅
      IsoAlgebra.mapOfNatIso e₁₃ ⋙ IsoAlgebra.mapOfNatIso e₃₄,
    ∀ K, (j.hom.app K).hom.f = a.hom.app K.carrier

/-- All fixed-pair clauses of the supplied system. The existential comparisons are
uniquely fixed by HEq to the actual finite and common comparisons in S; this merely
transports their dependent types to the supplied stage-family endpoints. It introduces
no arbitrary coefficient map. The source family is identified with the actual pullback
by S.sfFinite and S.sfPair, and the coefficient functors by S.finite_functor and
S.pair_functor.
Source: trace-definition final sentence, auxiliary proof steps 4--10
(blueprint: lem-fd-frobenius-fixed-pair-comparison). -/
def FdFixedPairComparison : Prop :=
  (IsoAlgebra.mapOfNatIso (S.pullback g).pair).IsEquivalence ∧
  (∀ E, (IsoAlgebra.mapOfNatIso ((S.pullback g).finite E).rational).IsEquivalence) ∧
  ∃ (b : ∀ E : Padic.FiniteCoefficientFields l Ω,
      (S.coefficients T).family.Φ E ⋙ (pbcQbarPullFamily l Ω g.hom).Φ E ≅
        (S.pullback g).sfFamily.Φ E ⋙ (S.coefficients T).family.Φ E)
    (c : (S.coefficients T).family.functor ⋙ (pbcQbarPullFamily l Ω g.hom).functor ≅
      (S.pullback g).sfFamily.functor ⋙ (S.coefficients T).family.functor),
    (∀ E, HEq (b E) ((S.pullback g).finite E).rational) ∧
    HEq c (S.pullback g).pair ∧
    (∀ (E L : Padic.FiniteCoefficientFields l Ω) (e : E ≤ L),
      FdFixedPairSquare ((S.pullback g).sfFamily.β e).symm (b L) (b E)
        ((pbcQbarPullFamily l Ω g.hom).β e).symm
        ((S.coefficients T).family.β e).symm) ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      FdFixedPairSquare ((S.pullback g).sfFamily.ιCompFunctorIso E) c (b E)
        ((pbcQbarPullFamily l Ω g.hom).ιCompFunctorIso E)
        ((S.coefficients T).family.ιCompFunctorIso E))

/-- The comparison on the recorded framework Weil categories, together with all
normalized compatibility squares. HEq only identifies different proof presentations
of the same actual pullback; it fixes the full functor, including its Hom map.
Source: trace-definition final sentence, auxiliary proof steps 4--10
(blueprint: lem-fd-frobenius-fixed-pair-comparison). -/
def FdGeometricFixedPairComparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] [IsNoetherian (D.geometricFiber X₀).left]
    [Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n)]
    [Fact (∀ x : (D.geometricFiber X₀).left,
      IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x))] : Prop :=
  FdFixedPairComparison l Ω S (D.geometricFiber X₀).left (D.geometricFrobenius X₀) ∧
  (∃ J : sfCommonStageWeilComplex D l hl X₀ Ω ≌
      IsoAlgebra (pbcQbarCompletedPull l Ω (D.geometricFrobenius X₀).hom),
    HEq J.functor (IsoAlgebra.mapOfNatIso (S.pullback (D.geometricFrobenius X₀)).pair)) ∧
  (∀ E : Padic.FiniteCoefficientFields l Ω,
    ∃ J : sfWeilComplex D l hl X₀ (pbcFiniteField.{u} l Ω E) ≌
        IsoAlgebra ((pbcQbarPullFamily l Ω (D.geometricFrobenius X₀).hom).Φ E),
      HEq J.functor
        (IsoAlgebra.mapOfNatIso ((S.pullback (D.geometricFrobenius X₀)).finite E).rational))

/-- The geometric fibre satisfies all coefficient-comparison hypotheses, and the
specified transport of Weil pairs is an equivalence compatible with scalar extension
and finite-stage inclusions. No k-linearity of geometric Frobenius is required.
Source: blueprint main-20261015, trace-definition final sentence
(blueprint: lem-fd-frobenius-fixed-pair-comparison).

Proof:
1. Base change the separated finite-type structure morphism to k, using
   lem-pod-separated-finite-type-base-change. Finite generation is preserved even
   though the algebraic closure need not be finite over the base field.
2. A field is noetherian; finite type over it gives noetherianity by
   lem-weil-pbc-finite-type-over-noetherian. Apply lem-kun-dimension-finite-type to
   obtain a natural-number dimension bound, also valid for the empty scheme.
3. Since l and p are distinct primes, l is a unit in k, hence in every local ring
   of X. The recorded geometricFrobenius is the scheme automorphism with inverse
   id times Spec of arithmetic Frobenius; no k-linearity is used.
4. At a finite or common stage transport theta using the inverse of the forward
   pullback comparison, then J(theta). Both factors are isomorphisms.
5. Naturality of the comparison identifies the two intertwining conditions.
   Faithfulness reflects their equality. Thus the Hom map is exactly J restricted
   to intertwining arrows and is bijective, including its inverse restriction.
6. Given a target pair, essential surjectivity of J gives an underlying isomorphism
   from JK. Conjugate its structure to JK and lift it and its inverse through the
   Hom bijection. Faithfulness proves the inverse equations upstairs.
7. Apply lem-trf-fully-faithful-ess-surj-equivalence to this very pair functor.
8. The mixed scalar square is the given compatible transformation of stage systems
   in S, with its specified actual scalar and Frobenius comparisons.
9. Naturality of the coefficient scalar comparison at theta, combined with that
   square, says that its inverse component intertwines the transported structures.
   Its inverse intertwines too, giving the stated normalized natural isomorphism.
10. Apply the same calculation to stage inclusions and the common comparison's
    specified finite components. Naturality gives the inclusion isomorphisms.
    Identity and scalar cocycle equations lift because forgetting pairs is faithful. -/
theorem frobeniusFixedPairComparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] :
    ∃ (_hN : IsNoetherian (D.geometricFiber X₀).left)
      (_hD : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n))
      (_hI : Fact (∀ x : (D.geometricFiber X₀).left,
        IsUnit (l : (D.geometricFiber X₀).left.presheaf.stalk x))),
      @FdGeometricFixedPairComparison l _ Ω _ _ _ S D hl X₀ _ _ _ _hN _hD _hI := by
  sorry

end WeilConjectures
