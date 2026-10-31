/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurShiftedTateUnitScalarCoherence
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleLinear
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisons
public import WeilConjectures.AlgebraicGeometry.IntegralTwistDerivedScalarCanonical
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.NormalizedDVRTower
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison
public import Mathlib.Topology.KrullDimension

public import WeilConjectures.AlgebraicGeometry.CompletedLineTensorCoherence

public import WeilConjectures.AlgebraicGeometry.ConstantGeometricStalkUnit
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackShiftCoordinates

/-! # Integral operation domains and normalized source comparisons

Source: current Weil blueprint, sec-smooth-purity/sk-thm-purity-transport,
Proof Steps 2-3; extracted scalar-naturality argument, Steps 1-12
(blueprint: lem-pur-adic-operation-domains-source-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicOperationSource

variable (P : PurityFiniteSetting.{u})
  (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
  [FiniteDimensional (Padic P.coefficients.l) E]

/-- The input interval means this interval at every positive finite reduction.
Source: purity transport Steps 2-3
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def TorInterval (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource P.coefficients.l E W)) (r s : ℤ) : Prop :=
  ∀ n : ℕ, HasProEtaleTorAmplitude W
    (Padic.coefficientExtensionRing P.coefficients.l E (n + 1))
    ((scalarReductionDerivedExtension P.coefficients.l E W n).obj K) r s

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  (f : X ⟶ Y)

/-- The specified source H_E, with the existing completed pullback, line tensor and shift.
Source: purity transport Step 2
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def sourceFunctor (d : ℕ) :
    DerivedCategory (scalarReductionSource P.coefficients.l E Y) ⥤
      DerivedCategory (scalarReductionSource P.coefficients.l E X) :=
  letI := P.shiftedTateResidueInverse X
  integralDerivedPullback P.coefficients.l E f ⋙
    sfIntegralTwistingFunctor P.coefficients.l E X (d : ℤ) ⋙
      shiftFunctor _ (2 * (d : ℤ))

variable (F : Type u) [Field F] [Algebra (Padic P.coefficients.l) F]
  [FiniteDimensional (Padic P.coefficients.l) F]
  (ι : E →ₐ[Padic P.coefficients.l] F)

/-- Ordinary scalar/pullback balancing transported by the specified chi on both sides.
Its direction is C_X L_E to L_F C_Y. No tower identification is selected separately.
Source: purity transport Step 3, extracted proof Step 8
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def pullbackScalar (K : sfIntegralConstructibleCategory P.coefficients.l E Y) :
    (completedDerivedScalarExtension P.coefficients.l E F ι X).obj
        ((integralDerivedPullback P.coefficients.l E f).obj K.obj) ≅
      (integralDerivedPullback P.coefficients.l F f).obj
        ((completedDerivedScalarExtension P.coefficients.l E F ι Y).obj K.obj) :=
  letI := P.shiftedTateResidueInverse X
  letI := P.shiftedTateResidueInverse Y
  CompletedLineTensor.chi P.coefficients.l E X F ι _
      (CompletedLineTensor.intrinsic_complete P.coefficients.l E X
        ((constructibleIntegralPullback P.coefficients.l E f).obj K)) ≪≫
    (sfIntegralConstructible P.coefficients.l F X).ι.mapIso
      (integralPullbackScalarComparison P.coefficients.l E F ι f K) ≪≫
    (integralDerivedPullback P.coefficients.l F f).mapIso
      (CompletedLineTensor.chi P.coefficients.l E Y F ι K.obj
        (CompletedLineTensor.intrinsic_complete P.coefficients.l E Y K)).symm

/-- The prescribed a: scalar shift, then beta, then the twisted pullback comparison.
Source: purity transport Step 3, extracted proof Step 8
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def sourceComponent (d : ℕ)
    (K : sfIntegralConstructibleCategory P.coefficients.l E Y) :
    (completedDerivedScalarExtension P.coefficients.l E F ι X).obj
        ((sourceFunctor P E f d).obj K.obj) ≅
      (sourceFunctor P F f d).obj
        ((completedDerivedScalarExtension P.coefficients.l E F ι Y).obj K.obj) :=
  letI := P.shiftedTateResidueInverse X
  letI := P.shiftedTateResidueInverse Y
  (PurShiftedTate.shiftIso P.coefficients.l E F ι X (2 * (d : ℤ))).app
      ((sfIntegralTwistingFunctor P.coefficients.l E X (d : ℤ)).obj
        ((integralDerivedPullback P.coefficients.l E f).obj K.obj)) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((integralTwistOrdinaryBeta P.coefficients.l E F ι X (d : ℤ)).app
          ((constructibleIntegralPullback P.coefficients.l E f).obj K) ≪≫
        (sfIntegralTwistingFunctor P.coefficients.l F X (d : ℤ)).mapIso
          (pullbackScalar P E f F ι K))

/-- The finite-Tor categories inherit the existing constant-section scalar action.
Source: purity transport Step 2, linear domains
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
instance finiteTorLinear (W : Scheme.{u}) :
    Linear (Padic.coefficientExtensionIntegers P.coefficients.l E)
      (finiteTorConstructibleIntegralCategory P.coefficients.l E W) :=
  Linear.fullSubcategory (finiteTorConstructibleIntegral P.coefficients.l E W)

/-- The inherited triangulation is the dependency's actual finite-Tor triangulation.
Source: purity transport Step 2
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
instance finiteTorTriangulated (W : Scheme.{u}) :
    (finiteTorConstructibleIntegral P.coefficients.l E W).IsTriangulated :=
  ConstructibleExceptionalCoefficients.integralTriangulated P.coefficients.l { carrier := E } W

section Geometry
variable
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of P.field.k))]
  [Xs : IsSeparated (X ↘ Spec (.of P.field.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [Ys : IsSeparated (Y ↘ Spec (.of P.field.k))]
  [fb : f.IsOver (Spec (.of P.field.k))] [fs : IsSeparated f]
  [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (d : ℕ) [sm : SmoothOfRelativeDimension d f]
include Xft Xqc Xs Yft Yqc Ys fb fs fft fqc d sm

/-- Completed pullback, twist and shift preserve the asserted domains, with the
specified common reduction interval. Source: purity transport Step 2
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: reduction of completed pullback is finite-level pullback. Pullback preserves
constructibility and Tor interval, as does tensoring with the invertible Tate line.
Derived completeness follows from the normalized reduction realization. Reduction
commutes with shift, and cochain shift by 2d subtracts 2d from both endpoints.
These statements hold at every positive level with one interval. -/
theorem source_preserves :
    (∀ K : sfIntegralConstructibleCategory P.coefficients.l E Y,
      sfIntegralConstructible P.coefficients.l E X ((sourceFunctor P E f d).obj K.obj)) ∧
    (∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E Y,
      finiteTorConstructibleIntegral P.coefficients.l E X
        ((sourceFunctor P E f d).obj K.obj)) ∧
    ∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E Y) (r s : ℤ),
      r ≤ s → TorInterval P E Y K.obj r s →
      TorInterval P E X ((sourceFunctor P E f d).obj K.obj)
        (r - 2 * (d : ℤ)) (s - 2 * (d : ℤ)) := by
  sorry

/-- The restriction of the specified H, on both objects and maps.
Source: purity transport Step 2
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def sourceFiniteTor :
    finiteTorConstructibleIntegralCategory P.coefficients.l E Y ⥤
      finiteTorConstructibleIntegralCategory P.coefficients.l E X :=
  (finiteTorConstructibleIntegral P.coefficients.l E X).lift
    ((finiteTorConstructibleIntegral P.coefficients.l E Y).ι ⋙ sourceFunctor P E f d)
    (source_preserves P E f d).2.1

/-- Quantitative domains, triangulated closure, and linear exceptional adjunction.
The parameter S is the specified exceptional-operation system of the dependency;
its operations already include the adjunction, exactness, and normalized counit shifts.
Source: purity transport Steps 2-3
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: compact-support reduction is the proper/open reduction tower and has upper
bound s+2DX. The specified exceptional adjoint has lower bound r-2DX and upper bound
s+2DY. Both retain constructibility and completeness, so their output objects are in
the full finite-Tor categories. Reduction is exact and shift-compatible; apply the
finite Tor triangle criterion levelwise with common min/max endpoints to obtain their
triangulated closure. The existing full-subcategory adjunction supplies the same Hom
bijections and counit. The compact-support tower and its total derived limit are linear
on morphisms for constant integral scalars. The linear-right-adjoint argument makes G
linear, and its transpose formulas G(h) eta and epsilon P(v) make the Hom equivalence
linear in both directions. The adjoint shift is uniquely characterized by compatibility
of its counit with the fixed left shift. Empty schemes use the nonnegative bound zero. -/
theorem operationDomains
    (DX DY : ℕ) (hX : topologicalKrullDim X ≤ (DX : WithBot ℕ∞))
    (hY : topologicalKrullDim Y ≤ (DY : WithBot ℕ∞))
    (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := f)) (c : Compactification f) :
    let op := S.ring.operation c (.integral { carrier := E })
    (finiteTorConstructibleIntegral P.coefficients.l E X).IsTriangulated ∧
    (finiteTorConstructibleIntegral P.coefficients.l E Y).IsTriangulated ∧
    (∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E X) (r s : ℤ),
      r ≤ s → TorInterval P E X K.obj r s →
      TorInterval P E Y (op.F.obj K).obj r (s + 2 * (DX : ℤ))) ∧
    (∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E Y) (r s : ℤ),
      r ≤ s → TorInterval P E Y K.obj r s →
      TorInterval P E X (op.G.obj K).obj (r - 2 * (DX : ℤ)) (s + 2 * (DY : ℤ))) ∧
    op.F.Linear (Padic.coefficientExtensionIntegers P.coefficients.l E) ∧
    op.G.Linear (Padic.coefficientExtensionIntegers P.coefficients.l E) ∧
    (∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E X)
      (M : finiteTorConstructibleIntegralCategory P.coefficients.l E Y),
      ∃ e : (op.F.obj K ⟶ M) ≃ₗ[Padic.coefficientExtensionIntegers P.coefficients.l E]
          (K ⟶ op.G.obj M), e.toEquiv = op.adjunction.homEquiv K M) ∧
    (∀ g : op.G.CommShift ℤ,
      (letI : op.F.CommShift ℤ := op.leftShift
       letI : op.G.CommShift ℤ := g
       op.adjunction.counit.CommShift ℤ) → g = op.rightShift) := by
  sorry

set_option linter.unusedSectionVars false in
/-- The completed units and shifted Tate units have precisely the stated containing
intervals and belong to the finite-Tor domain. Source: purity transport Step 2
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: each positive reduction of the unit is the free rank-one coefficient module
in degree zero. The Tate line is locally free of rank one, so it has the same interval.
Reduction commutes with shift by 2d, giving the two endpoints -2d. Constant finite
coefficients are constructible and the normalized unit and line towers are complete. -/
theorem unitDomains : P.shiftedTateUnitDomain E X d ∧ P.shiftedTateUnitDomain E Y 0 := by
  exact ⟨(P.shiftedTateUnitScalarCoherence E E (AlgHom.id _ E) X d).2.1,
    (P.shiftedTateUnitScalarCoherence E E (AlgHom.id _ E) Y 0).2.1⟩

end Geometry

section ScalarDomains
variable (W : Scheme.{u}) [W.Over (Spec (.of P.field.k))]
  [Wft : LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
  [Wqc : QuasiCompact (W ↘ Spec (.of P.field.k))]
  [Ws : IsSeparated (W ↘ Spec (.of P.field.k))]
include Wft Wqc Ws

/-- Ordinary completed-ring scalar extension preserves completeness, constructibility
and every common reduction Tor interval, including for ramified extensions.
Source: purity transport Step 3
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: the completed coefficient sheaf is finite free, so chi identifies ordinary
extension with strict-tower extension and proves completeness. Tower extension preserves
constructibility. If e is the ramification index, levels en of the F tower are finite
free over level n of the E tower and retain [r,s]. At any m choose en at least m; tensor
associativity with every degree-zero module at level m proves the same interval there.
No flatness of a same-index ramified quotient map is assumed. -/
theorem scalar_preserves :
    (∀ K : sfIntegralConstructibleCategory P.coefficients.l E W,
      sfIntegralConstructible P.coefficients.l F W
        ((completedDerivedScalarExtension P.coefficients.l E F ι W).obj K.obj)) ∧
    (∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E W,
      finiteTorConstructibleIntegral P.coefficients.l F W
        ((completedDerivedScalarExtension P.coefficients.l E F ι W).obj K.obj)) ∧
    ∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E W) (r s : ℤ),
      r ≤ s → TorInterval P E W K.obj r s →
      TorInterval P F W
        ((completedDerivedScalarExtension P.coefficients.l E F ι W).obj K.obj) r s := by
  sorry

/-- The restriction uses ordinary scalar extension, not an independently chosen tower.
Source: purity transport Step 3
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def scalarConstructible : sfIntegralConstructibleCategory P.coefficients.l E W ⥤
    sfIntegralConstructibleCategory P.coefficients.l F W :=
  (sfIntegralConstructible P.coefficients.l F W).lift
    ((sfIntegralConstructible P.coefficients.l E W).ι ⋙
      completedDerivedScalarExtension P.coefficients.l E F ι W)
    (scalar_preserves P E F ι W).1

/-- The actual restriction on the uniform finite-Tor domain, with its inherited maps.
Source: purity transport Step 3
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def scalarFiniteTor : finiteTorConstructibleIntegralCategory P.coefficients.l E W ⥤
    finiteTorConstructibleIntegralCategory P.coefficients.l F W :=
  (finiteTorConstructibleIntegral P.coefficients.l F W).lift
    ((finiteTorConstructibleIntegral P.coefficients.l E W).ι ⋙
      completedDerivedScalarExtension P.coefficients.l E F ι W)
    (scalar_preserves P E F ι W).2.1

end ScalarDomains

/-- The ordinary scalar restriction is exact for the canonical scalar shift.
Source: purity transport Step 3
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: ordinary derived extension is exact with the shift descending its termwise
K-flat tensor. Restrict to the full triangulated subcategories using scalar_preserves.
The universal-counit normalization uniquely identifies this shift with the published
PurShiftedTate.shiftIso. Thus the displayed inclusion square fixes its normalization. -/
theorem scalar_exact (W : Scheme.{u}) [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [IsSeparated (W ↘ Spec (.of P.field.k))] :
    ∃ h : (scalarFiniteTor P E F ι W).CommShift ℤ,
      (letI := h; (scalarFiniteTor P E F ι W).IsTriangulated) ∧
      ∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E W) (m : ℤ),
        (finiteTorConstructibleIntegral P.coefficients.l F W).ι.map
            ((Functor.commShiftIso (scalarFiniteTor P E F ι W) (self := h) m).hom.app K) ≫
          ((finiteTorConstructibleIntegral P.coefficients.l F W).ι.commShiftIso m).hom.app
            ((scalarFiniteTor P E F ι W).obj K) =
        (completedDerivedScalarExtension P.coefficients.l E F ι W).map
          (((finiteTorConstructibleIntegral P.coefficients.l E W).ι.commShiftIso m).hom.app K) ≫
          (PurShiftedTate.shiftIso P.coefficients.l E F ι W m).hom.app K.obj := by
  sorry

/-- The canonical H shift: pullback descent, termwise line shift, then interchange
with the even shift 2d. Source: purity transport Step 2 and extracted Step 10
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def sourceShift (e : (integralDerivedPullback P.coefficients.l E f).CommShift ℤ)
    (d : ℕ) (m : ℤ)
    (K : DerivedCategory (scalarReductionSource P.coefficients.l E Y)) :
    (sourceFunctor P E f d).obj (K⟦m⟧) ≅ ((sourceFunctor P E f d).obj K)⟦m⟧ :=
  letI := P.shiftedTateResidueInverse X
  (shiftFunctor _ (2 * (d : ℤ))).mapIso
    ((sfIntegralTwistingFunctor P.coefficients.l E X (d : ℤ)).mapIso
        ((Functor.commShiftIso (integralDerivedPullback P.coefficients.l E f)
          (self := e) m).app K) ≪≫
      ((sfIntegralTwistingFunctor P.coefficients.l E X (d : ℤ)).commShiftIso m).app
        ((integralDerivedPullback P.coefficients.l E f).obj K)) ≪≫
    (shiftFunctorComm _ m (2 * (d : ℤ))).app
      ((sfIntegralTwistingFunctor P.coefficients.l E X (d : ℤ)).obj
        ((integralDerivedPullback P.coefficients.l E f).obj K))

/-- The source comparison is natural on the actual constructible category.
Source: purity transport Step 3, extracted Step 8
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: each factor defining sourceComponent is a component of a natural comparison:
the universal scalar shift, the balanced line scalar comparison beta, and pullback
balancing transported by the specified natural chi. Naturality is preserved by
whiskering and composition, giving the displayed square for every derived morphism. -/
theorem source_naturality (d : ℕ)
    {K M : sfIntegralConstructibleCategory P.coefficients.l E Y} (v : K ⟶ M) :
    (completedDerivedScalarExtension P.coefficients.l E F ι X).map
        ((sourceFunctor P E f d).map v.hom) ≫ (sourceComponent P E f F ι d M).hom =
      (sourceComponent P E f F ι d K).hom ≫
        (sourceFunctor P F f d).map
          ((completedDerivedScalarExtension P.coefficients.l E F ι Y).map v.hom) := by
  sorry

/-- The natural isomorphism a has the prescribed, fully constructed components.
Source: purity transport Step 3
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def sourceComparison (d : ℕ) :
    (sfIntegralConstructible P.coefficients.l E Y).ι ⋙ sourceFunctor P E f d ⋙
        completedDerivedScalarExtension P.coefficients.l E F ι X ≅
      (sfIntegralConstructible P.coefficients.l E Y).ι ⋙
        completedDerivedScalarExtension P.coefficients.l E F ι Y ⋙ sourceFunctor P F f d :=
  NatIso.ofComponents (sourceComponent P E f F ι d) (source_naturality P E f F ι d)

/-- Canonical identification H_E(1_Y) with T_E, using the normalized pullback unit.
Source: purity transport Step 2 and extracted Step 11
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def sourceUnit (d : ℕ) :
    (sourceFunctor P E f d).obj (integralConstantCoefficientObject P.coefficients.l E Y) ≅
      P.shiftedTateUnit E X d :=
  letI := P.shiftedTateResidueInverse X
  (shiftFunctor _ (2 * (d : ℤ))).mapIso
    ((sfIntegralTwistingFunctor P.coefficients.l E X (d : ℤ)).mapIso
      (ConstantGeometricStalkUnit.integralUnit P.coefficients.l E f))

section GeometryComparisons
variable
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of P.field.k))]
  [Xs : IsSeparated (X ↘ Spec (.of P.field.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [Ys : IsSeparated (Y ↘ Spec (.of P.field.k))]
  [fb : f.IsOver (Spec (.of P.field.k))] [fs : IsSeparated f]
  [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (d : ℕ) [sm : SmoothOfRelativeDimension d f]
include Xft Xqc Xs Yft Yqc Ys fb fs fft fqc d sm

/-- H is exact and integral-linear, with its shift fixed by the signed pullback
coordinates and termwise line tensor. Source: purity transport Step 2
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: finite type over the field is Noetherian and finite-dimensional. The ordinary
derived pullback comparison is therefore invertible on constructible inputs. Ordinary
pullback is exact and integral-linear, and line tensor and shift have the same
properties. Their composite is H. The Roos cochain shift has the signed coordinates
specified in ShiftCoordinates; localization gives ShiftDescent. Its composite with
the line shift and even integer-shift interchange is sourceShift. Full-subcategory
restriction retains these maps and the distinguished triangles. -/
theorem source_exact_linear :
    ∃ (c : (integralOperationsPullbackComplexFunctor P.coefficients.l E f).CommShift ℤ)
      (e : (integralDerivedPullback P.coefficients.l E f).CommShift ℤ)
      (h : (sourceFiniteTor P E f d).CommShift ℤ),
      IntegralCompletedComparison.ShiftCoordinates P.coefficients.l E f c ∧
      IntegralCompletedComparison.ShiftDescent P.coefficients.l E f c e ∧
      (letI := h; (sourceFiniteTor P E f d).IsTriangulated) ∧
      (sourceFiniteTor P E f d).Linear
        (Padic.coefficientExtensionIntegers P.coefficients.l E) ∧
      ∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l E Y) (m : ℤ),
        (finiteTorConstructibleIntegral P.coefficients.l E X).ι.map
            ((Functor.commShiftIso (sourceFiniteTor P E f d) (self := h) m).hom.app K) ≫
          ((finiteTorConstructibleIntegral P.coefficients.l E X).ι.commShiftIso m).hom.app
            ((sourceFiniteTor P E f d).obj K) =
        (sourceFunctor P E f d).map
          (((finiteTorConstructibleIntegral P.coefficients.l E Y).ι.commShiftIso m).hom.app K) ≫
          (sourceShift P E f e d m K.obj).hom := by
  sorry

/-- Restriction of a to the full uniform finite-Tor categories has exactly the
prescribed ambient components; this condition determines it uniquely.
Source: purity transport Steps 2-3
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: source_preserves and scalar_preserves put both endpoint composites in the
finite-Tor categories. Lift each sourceComponent and its inverse through the full
inclusion. Their inverse equations and naturality are the ambient equations, reflected
by its faithfulness. The same faithfulness gives uniqueness componentwise. -/
theorem sourceFiniteComparison_existsUnique :
    ∃! a : sourceFiniteTor P E f d ⋙ scalarFiniteTor P E F ι X ≅
        scalarFiniteTor P E F ι Y ⋙ sourceFiniteTor P F f d,
      ∀ K : finiteTorConstructibleIntegralCategory P.coefficients.l E Y,
        (finiteTorConstructibleIntegral P.coefficients.l F X).ι.map (a.hom.app K) =
          (sourceComponent P E f F ι d
            ((PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l E Y).obj K)).hom :=
              by
  let a : sourceFiniteTor P E f d ⋙ scalarFiniteTor P E F ι X ≅
      scalarFiniteTor P E F ι Y ⋙ sourceFiniteTor P F f d :=
    NatIso.ofComponents
      (fun K ↦ (finiteTorConstructibleIntegral P.coefficients.l F X).isoMk
        (sourceComponent P E f F ι d
          ((PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l E Y).obj K)))
      (by
        intro K M v
        apply ObjectProperty.hom_ext
        exact source_naturality P E f F ι d
          ((PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l E Y).map v))
  refine ⟨a, fun K ↦ rfl, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact hb K

/-- The actual comparison a on D^b_ctf, fixed by its previously constructed components.
Source: purity transport Step 3
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def sourceFiniteComparison :
    sourceFiniteTor P E f d ⋙ scalarFiniteTor P E F ι X ≅
      scalarFiniteTor P E F ι Y ⋙ sourceFiniteTor P F f d :=
  (sourceFiniteComparison_existsUnique P E f F ι d).exists.choose

variable (L : Type u) [Field L] [Algebra (Padic P.coefficients.l) L]
  [FiniteDimensional (Padic P.coefficients.l) L] (j : F →ₐ[Padic P.coefficients.l] L)

/-- The exact source comparison obeys the ordinary tensor-associator cocycle.
Source: purity transport Step 3, extracted Step 9
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: expand both successive comparisons before the final even shift. Naturality of
beta exchanges the middle theta and beta factors; the beta and theta coefficient
cocycles then combine the two comparisons. All remaining associators are the ordinary
tensor associators, normalized by their universal counits under chi. Finally apply the
coherent scalar shift. This gives the displayed equality in composition order. -/
theorem source_composition (K : sfIntegralConstructibleCategory P.coefficients.l E Y) :
    ((CompletedLineTensor.associatorData P.coefficients.l E X F ι L j).derived.hom.app
        ((sourceFunctor P E f d).obj K.obj)) ≫
        (sourceComponent P E f L (j.comp ι) d K).hom =
      (completedDerivedScalarExtension P.coefficients.l F L j X).map
          (sourceComponent P E f F ι d K).hom ≫
        (sourceComponent P F f L j d ((scalarConstructible P E F ι Y).obj K)).hom ≫
        (sourceFunctor P L f d).map
          ((CompletedLineTensor.associatorData P.coefficients.l E Y F ι L j).derived.hom.app
            K.obj) := by
  sorry

/-- Repeated coefficients give identity under the ordinary multiplication unitors.
Source: purity transport Step 3, extracted Step 9
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: the pullback coefficient comparison and the line balancing comparison at the
identity algebra map are their unit maps. Substitute these into sourceComponent and
use their unit triangles and the normalized scalar shift. The resulting equality is
precisely the ordinary tensor-unitor square displayed here. -/
theorem source_identity (K : sfIntegralConstructibleCategory P.coefficients.l E Y) :
    (sourceComponent P E f E (AlgHom.id _ E) d K).hom ≫
        (sourceFunctor P E f d).map
          ((CompletedLineTensor.ordinaryUnit P.coefficients.l E Y).hom.app K.obj) =
      (CompletedLineTensor.ordinaryUnit P.coefficients.l E X).hom.app
        ((sourceFunctor P E f d).obj K.obj) := by
  sorry

/-- At the coefficient unit a is exactly the specified shifted-Tate comparison q.
Source: purity transport Step 3, extracted Step 11
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: the normalized pullback unit identifies L_E(1_Y) with 1_X. On a representative,
pullback/scalar balancing at the unit is inverse multiplication. Combining it with
coefficient multiplication in Y gives coefficient multiplication in X. Substitute this
unit square into the definition of sourceComponent. The remaining factors are beta,
the canonical coefficient-unit map and scalar shift, exactly shiftedTateScalarIso. -/
theorem source_at_unit :
    let K := constantWeilIntegralObject P.coefficients.l E P.field P.coefficients.different Y
    (sourceComponent P E f F ι d K).hom ≫
        (sourceFunctor P F f d).map
          (PurShiftedTate.unitIso P.coefficients.l E F ι Y P.field
            P.coefficients.different).hom ≫ (sourceUnit P F f d).hom =
      (completedDerivedScalarExtension P.coefficients.l E F ι X).map
          (sourceUnit P E f d).hom ≫ (P.shiftedTateScalarIso E X F ι d).hom := by
  sorry

/-- The prescribed comparison commutes with the canonical shifts in the input.
The shifts eE and eF are required to descend the actual signed cochain coordinates;
this does not allow a free choice of shift on H. Source: purity transport Step 3
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: theta commutes with the normalized pullback/scalar shifts by framework shift
compatibility. On K-flat flat-term representatives beta sends (x tensor l) tensor b
to (x tensor b) tensor (l tensor 1); the line and scalar factors have degree zero, so
shifting x introduces no extra sign. The final interchange with shift 2d has sign
(-1)^(2dm)=1. Chi respects the same shifts. Compose these squares to obtain the equation. -/
theorem source_shift
    (cE : (integralOperationsPullbackComplexFunctor P.coefficients.l E f).CommShift ℤ)
    (eE : (integralDerivedPullback P.coefficients.l E f).CommShift ℤ)
    (hcE : IntegralCompletedComparison.ShiftCoordinates P.coefficients.l E f cE)
    (heE : IntegralCompletedComparison.ShiftDescent P.coefficients.l E f cE eE)
    (cF : (integralOperationsPullbackComplexFunctor P.coefficients.l F f).CommShift ℤ)
    (eF : (integralDerivedPullback P.coefficients.l F f).CommShift ℤ)
    (hcF : IntegralCompletedComparison.ShiftCoordinates P.coefficients.l F f cF)
    (heF : IntegralCompletedComparison.ShiftDescent P.coefficients.l F f cF eF)
    (K : sfIntegralConstructibleCategory P.coefficients.l E Y) (m : ℤ) :
    (sourceComponent P E f F ι d (K⟦m⟧)).hom ≫
        (sourceFunctor P F f d).map
          ((completedDerivedScalarExtension P.coefficients.l E F ι Y).map
              (((sfIntegralConstructible P.coefficients.l E Y).ι.commShiftIso m).hom.app K) ≫
            (PurShiftedTate.shiftIso P.coefficients.l E F ι Y m).hom.app K.obj) ≫
        (sourceShift P F f eF d m
          ((completedDerivedScalarExtension P.coefficients.l E F ι Y).obj K.obj)).hom =
      (completedDerivedScalarExtension P.coefficients.l E F ι X).map
          ((sourceFunctor P E f d).map
              (((sfIntegralConstructible P.coefficients.l E Y).ι.commShiftIso m).hom.app K) ≫
            (sourceShift P E f eE d m K.obj).hom) ≫
        (PurShiftedTate.shiftIso P.coefficients.l E F ι X m).hom.app
          ((sourceFunctor P E f d).obj K.obj) ≫
        (sourceComponent P E f F ι d K).hom⟦m⟧' := by
  sorry

/-- The two ordinary scalar models use the same scalar-extension witness and universal
K-flat counit in this size convention. This is the identity identification, not a new
choice of comparison. Source: purity transport Step 3, compact-support scalar notation
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def compactScalarModel (W : Scheme.{u}) :
    completedDerivedScalarExtension P.coefficients.l E F ι W ≅
      pbcDerivedExtend (completedCoefficientMap P.coefficients.l E F ι W) :=
  Iso.refl _

/-- The compact-support map c is precisely the recorded coefficient comparison,
with its existing proper/open, unit, composition, projection, reduction and shift
normalizations. Source: purity transport Step 3
(blueprint: lem-pur-adic-operation-domains-source-comparison). -/
def compactSupportComparison (c : Compactification f) :
    PurCompactSupport.recordedSupport P.coefficients.l E P.field
        P.coefficients.different f c ⋙
      completedDerivedScalarExtension P.coefficients.l E F ι Y ≅
    scalarFiniteTor P E F ι X ⋙
      PurCompactSupport.recordedSupport P.coefficients.l F P.field
        P.coefficients.different f c :=
  PurCompactSupport.recordedComparisonIso P.coefficients.l E F ι P.field
    P.coefficients.different f c

set_option linter.unusedSectionVars false in
/-- The specified compact-support scalar map is exact for the published canonical
scalar and proper/open shifts. All other normalizations remain those of the same
recordedComparisonIso, rather than separately chosen isomorphisms.
Source: purity transport Step 3, extracted Step 12
(blueprint: lem-pur-adic-operation-domains-source-comparison).

Proof: the scalar comparison is the proper adjunction mate of the coefficient
comparison after exact open extension. Their termwise scalar maps commute with shift;
the universal derived counits descend this square. Whiskering, taking the natural
inverse, and the normalized recorded-support identifications preserve the square.
The unit, composition, projection and finite-reduction formulas are those of the
specified compact-support comparison theorem, with these same maps. -/
theorem compactSupport_exact (c : Compactification f) :
    (PurCompactSupport.comparison
      (PurCompactSupport.completedChange P.coefficients.l E F ι) c).CommShift ℤ := by
  exact PurCompactSupport.comparison_commShift _ c

end GeometryComparisons
end WeilConjectures.AdicOperationSource
