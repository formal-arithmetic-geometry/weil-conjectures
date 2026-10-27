/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.SixFunctorDualNotation
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.Paper.EtaleCompactSupportCoefficientChange
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison

import Sheaf.Paper.FiniteTorStability
import all Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.ProjectionScalarSquare
import Sheaf.Paper.FiniteProjectionPresentation
import Sheaf.Paper.PfReductionProperOpenIdentities
import Sheaf.Paper.ProjectionReductionWitnessedFlatDomains
import all Sheaf.SecSmoothPurity.ReductionDirectImage

/-!
# Projection formula and finite coefficient reduction

Source: current blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-pf-reduction/prop-sf-pf-reduction (blueprint: prop-sf-pf-reduction).
The exponents are indexed by n+1 and m+1, so all positive levels, including
identity reduction, occur. All arrows use the existing normalized ringed operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The existing counit/open projection at the positive finite level, in intrinsic
constant-ring coordinates. The tensor presentations are the recorded normalized ones.
Source: blueprint prop-sf-pf-reduction, maps PF (blueprint: prop-sf-pf-reduction). -/
def finiteReductionProjection (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (L : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1))) :=
  ((projectionMap (finite l E (n + 1) (Nat.succ_pos n)) c
    (pullbackTensorFiniteModel l E X n) (pullbackTensorFiniteModel l E c.Z n)
    (pullbackTensorFiniteModel l E Y n)
    (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
      (Padic.coefficientExtensionRing l E (n + 1))).symm).app K).app L

/-- The left vertical arrow u: tensor reduction followed by compact-support reduction
on its first tensor factor. Source: blueprint prop-sf-pf-reduction, proof step 2
(blueprint: prop-sf-pf-reduction). -/
def finiteProjectionReductionSource (m n : ℕ) (h : m ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (L : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1))) :=
  (scalarTensor
    ((finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
      (Nat.succ_le_succ h)).map Y)
    (pullbackTensorFiniteModel l E Y n) (pullbackTensorFiniteModel l E Y m)).hom.app
      ((image (finite l E (n + 1) (Nat.succ_pos n)) c).obj K, L) ≫
    (pullbackTensorFiniteModel l E Y m).tensor.map (Prod.mkHom
      ((comparison
        (finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
          (Nat.succ_le_succ h)) c).app K) (𝟙 _))

/-- The right vertical arrow v: compact-support reduction, then compact support of
tensor reduction followed by the pullback comparison. Source: blueprint
prop-sf-pf-reduction, proof step 2 (blueprint: prop-sf-pf-reduction). -/
def finiteProjectionReductionTarget (m n : ℕ) (h : m ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (L : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1))) :=
  (comparison
    (finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
      (Nat.succ_le_succ h)) c).app
        ((pullbackTensorFiniteModel l E X n).tensor.obj
          (K, (pull (finite l E (n + 1) (Nat.succ_pos n)) f).obj L)) ≫
    (image (finite l E (m + 1) (Nat.succ_pos m)) c).map
      ((scalarTensor
        ((finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
          (Nat.succ_le_succ h)).map X)
        (pullbackTensorFiniteModel l E X n) (pullbackTensorFiniteModel l E X m)).hom.app
          (K, (pull (finite l E (n + 1) (Nat.succ_pos n)) f).obj L) ≫
        (pullbackTensorFiniteModel l E X m).tensor.map (Prod.mkHom (𝟙 _)
          ((scalarPull
            (finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
              (Nat.succ_le_succ h)) f).hom.app L)))

attribute [local irreducible] sfIntrinsicDerivedEquivalence pullbackTensorFiniteModel
  coefficientFiniteQuotientDerived CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor


private theorem quotient_restriction (W : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    normalizedDVRRes l E W h =
      pbcDerivedRestrict
        ((finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n)
          (Nat.succ_pos m) (Nat.succ_le_succ h)).map W) := by
  rw [sfStabilityQuotientRestrictionEquality l E W h]
  rfl

private theorem quotient_domain
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    {m n : ℕ} (h : m ≤ n)
    (K : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1)))
    (hK : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) W K) :
    finiteTorConstructible l E (m + 1) (Nat.succ_pos m) W
      ((pbcDerivedExtend
        ((finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n)
          (Nat.succ_pos m) (Nat.succ_le_succ h)).map W)).obj K) := by
  have ha :=
    (coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus.adjunction h
  rw [quotient_restriction l E W h] at ha
  let e : coefficientFiniteQuotientDerived l E W h ≅
      pbcDerivedExtend
        ((finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n)
          (Nat.succ_pos m) (Nat.succ_le_succ h)).map W) :=
    ha.leftAdjointUniq (pbcDerivedScalarAdjunction
    ((finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n)
      (Nat.succ_pos m) (Nat.succ_le_succ h)).map W))
  have hd := (finiteTor_stability_quotients D l hl E W h).1 K hK
  have ei : (coefficientFiniteQuotientDerived l E W h).obj K ≅
      (pbcDerivedExtend
        ((finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n)
          (Nat.succ_pos m) (Nat.succ_le_succ h)).map W)).obj K := e.app K
  have hc : intrinsicFiniteTorsionConstructible l E (m + 1) (Nat.succ_pos m) W
      ((pbcDerivedExtend
        ((finiteQuotientChange l E (n + 1) (m + 1) (Nat.succ_pos n)
          (Nat.succ_pos m) (Nat.succ_le_succ h)).map W)).obj K) := by
    constructor
    · exact Set.Finite.subset hd.1.1 (fun i hi ↦ by
        exact (not_congr ((DerivedCategory.homologyFunctor
          (proEtaleRingModules W (proEtaleConstantRing W
            (Padic.coefficientExtensionRing l E (m + 1)))) i).mapIso ei).isZero_iff.symm).mp hi)
    · intro i
      exact (intrinsicConstructible_of_iso W
        (Padic.coefficientExtensionRing l E (m + 1))
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules W (proEtaleConstantRing W
            (Padic.coefficientExtensionRing l E (m + 1)))) i).mapIso ei) (hd.1.2 i))
  refine ⟨hc, ?_⟩
  obtain ⟨a, b, hab, ht⟩ := hd.2
  refine ⟨a, b, hab, ?_⟩
  intro _A P eA f hf hP M i hi
  exact ht _A P ⟨eA.some ≪≫ ei.symm⟩ f hf hP M i hi

/-- The reduction square for the specified projection map commutes, and the original
projection is invertible exactly when the projection at the reduced objects is.
Source: current blueprint prop-sf-pf-reduction (blueprint: prop-sf-pf-reduction).

Proof:
1. Descend K,L to bounded constructible etale representatives
   (lem-sf-proetale-constructible-origin), retaining Tor bounds
   (lem-sf-comparison-tor-amplitude). Bounded flat constructible models
   (lem-sf-flat-model) show their reductions and tensor/pullback inputs have finite Tor.
2. Form u and v from lem-fix-operation-reduction and
   lem-fix-compact-support-coefficient-change; these are the two maps defined above.
3. Choose the displayed Nagata compactification (thm-nagata-compactification).
   Extension by zero preserves finite Tor (lem-trf-open-ctf), and the open projection
   isomorphism identifies the proper-factor tensor input
   (lem-cbc-extension-zero-projection-formula).
4. Write PF as the proper counit mate followed by proper image of the open tensor
   comparison (def-exchange-projection, def-sf-pf). The coefficient comparison is the
   proper mate followed by the open comparison (det-sp-reduction-direct-image).
5. Apply lem-weil-pbc-ringed-exchange-tensor-coherence to the coefficient-change square
   on the proper factor. It requires neither a Cartesian square nor quotient flatness.
6. Apply lem-sf-open-tensor-normalization to the open factor with underlying map the
   identity. Restriction is faithful on the essential image of extension by zero;
   the normalized comparisons restrict to identities. Tensor coherence gives equality.
7. Paste the proper and open equalities, using naturality of the coefficient map,
   obtaining precisely rho(PF) followed by v equals u followed by PF at level m+1.
8. Cancel u,v for the reduced map. For the assertion about the original map, both
   finite-coefficient projection maps are invertible by thm-sf-pf-finite and the
   witnessed pro-etale clause of lem-weil-finite-compact-projection-formula. -/
theorem projectionFiniteReduction
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (m n : ℕ) (h : m ≤ n) (_S : SixFunctorDatum D C E (n + 1) (Nat.succ_pos n))
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    (c : Compactification f.hom.left)
    (K : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)))
    (L : proEtaleDerivedCategory Y.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)))
    (_hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left K)
    (_hL : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y.obj.left L) :
    ((pbcDerivedExtend
      ((finiteQuotientChange C.l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
        (Nat.succ_le_succ h)).map Y.obj.left)).map (finiteReductionProjection C.l E n c K L) ≫
      finiteProjectionReductionTarget C.l E m n h c K L =
        finiteProjectionReductionSource C.l E m n h c K L ≫
          finiteReductionProjection C.l E m c
            ((pbcDerivedExtend
              ((finiteQuotientChange C.l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
                (Nat.succ_le_succ h)).map X.obj.left)).obj K)
            ((pbcDerivedExtend
              ((finiteQuotientChange C.l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
                (Nat.succ_le_succ h)).map Y.obj.left)).obj L)) ∧
    (IsIso (finiteReductionProjection C.l E n c K L) ↔
      IsIso (finiteReductionProjection C.l E m c
        ((pbcDerivedExtend
          ((finiteQuotientChange C.l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
            (Nat.succ_le_succ h)).map X.obj.left)).obj K)
        ((pbcDerivedExtend
          ((finiteQuotientChange C.l E (n + 1) (m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
            (Nat.succ_le_succ h)).map Y.obj.left)).obj L))) := by
  let : X.obj.left.Over (Spec (.of D.k)) := ⟨X.obj.hom⟩
  let : Y.obj.left.Over (Spec (.of D.k)) := ⟨Y.obj.hom⟩
  have : IsSeparated (X.obj.left ↘ Spec (.of D.k)) := by
    change IsSeparated X.obj.hom
    infer_instance
  have : IsSeparated (Y.obj.left ↘ Spec (.of D.k)) := by
    change IsSeparated Y.obj.hom
    infer_instance
  have : LocallyOfFiniteType X.obj.hom := X.property.1
  have : QuasiCompact X.obj.hom := X.property.2
  have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    infer_instance
  have : LocallyOfFiniteType f.hom.left :=
    locallyOfFiniteType_of_comp f.hom.left Y.obj.hom
  have : QuasiCompact (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    infer_instance
  have : QuasiCompact f.hom.left :=
    QuasiCompact.of_comp f.hom.left Y.obj.hom
  constructor
  · have hc := projection_factor_coordinates D C E m n h X Y f c
      (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
        (Padic.coefficientExtensionRing C.l E (n + 1))).symm
      (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
        (Padic.coefficientExtensionRing C.l E (m + 1))).symm
      (pullbackTensorFiniteModel C.l E X.obj.left n)
      (pullbackTensorFiniteModel C.l E c.Z n)
      (pullbackTensorFiniteModel C.l E Y.obj.left n)
      (pullbackTensorFiniteModel C.l E X.obj.left m)
      (pullbackTensorFiniteModel C.l E c.Z m)
      (pullbackTensorFiniteModel C.l E Y.obj.left m) K L _hK _hL
    have he := projection_scalar_square
      (finiteQuotientChange C.l E (n + 1) (m + 1) (Nat.succ_pos n)
        (Nat.succ_pos m) (Nat.succ_le_succ h)) c
      (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
        (Padic.coefficientExtensionRing C.l E (n + 1))).symm
      (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
        (Padic.coefficientExtensionRing C.l E (m + 1))).symm
      (pullbackTensorFiniteModel C.l E X.obj.left n)
      (pullbackTensorFiniteModel C.l E c.Z n)
      (pullbackTensorFiniteModel C.l E Y.obj.left n)
      (pullbackTensorFiniteModel C.l E X.obj.left m)
      (pullbackTensorFiniteModel C.l E c.Z m)
      (pullbackTensorFiniteModel C.l E Y.obj.left m) K L hc
    simpa only [finiteReductionProjection, finiteProjectionReductionSource,
      finiteProjectionReductionTarget, mixedChange, Category.assoc] using he
  · have : LocallyOfFiniteType Y.obj.hom := Y.property.1
    have : QuasiCompact Y.obj.hom := Y.property.2
    have : LocallyOfFiniteType (X.obj.left ↘ Spec (.of D.k)) := X.property.1
    have : QuasiCompact (X.obj.left ↘ Spec (.of D.k)) := X.property.2
    have : LocallyOfFiniteType (Y.obj.left ↘ Spec (.of D.k)) := Y.property.1
    have : QuasiCompact (Y.obj.left ↘ Spec (.of D.k)) := Y.property.2
    have hKn : IsIso (finiteReductionProjection C.l E n c K L) := by
      exact finiteProjectionPresentation_isIso D C E n X Y f c
        (pullbackTensorFiniteModel C.l E X.obj.left n)
        (pullbackTensorFiniteModel C.l E c.Z n)
        (pullbackTensorFiniteModel C.l E Y.obj.left n) K L _hK _hL
    have hKm := finiteProjectionPresentation_isIso D C E m X Y f c
      (pullbackTensorFiniteModel C.l E X.obj.left m)
      (pullbackTensorFiniteModel C.l E c.Z m)
      (pullbackTensorFiniteModel C.l E Y.obj.left m) _ _
      (quotient_domain C.l E D C.different X.obj.left h K _hK)
      (quotient_domain C.l E D C.different Y.obj.left h L _hL)
    exact ⟨fun _ ↦ hKm, fun _ ↦ hKn⟩

end WeilConjectures
