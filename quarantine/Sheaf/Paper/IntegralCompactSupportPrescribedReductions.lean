/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Compactification.BoundaryPreparation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
import Sheaf.Paper.SfIntegralReductionTower
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
import Sheaf.Paper.NormalizedDVRTower
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.EtaleCompactSupportCoefficientChange
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Integral compact supports have the prescribed reductions

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2135 (blueprint: lem-coef-integral-compact-support).

The integral value is specified by a Roos triangle of the very tower used in
`sfIntegralCompactSupportValue`. Specifying its projection retains the data needed
for the canonical coefficient maps, which are their tensor/restriction adjoints.
The result applies to every realization of that defining derived limit, including
its chosen value, and imposes no extra condition on the input. Natural index n
always denotes the positive exponent n+1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- Countable products for the defining compact-support tower, obtained from the
recorded completed-coefficient derived products, with no extra existence assumption.
Source: blueprint order 2135, Proof paragraph 2; Stacks Tag 07KC
(blueprint: lem-coef-integral-compact-support). -/
noncomputable instance coefCompactSupportHasProduct
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    HasProduct (sfCompactSupportTerm l E c K) := by
  let : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    integralOperationsDerivedCountableProducts l E Y
  infer_instance

/-- The finite-level compact-support transition before restricting to completed
coefficients. Apply the higher-level functor to the actual quotient-induced reduction
map, then the normalized compact-support restriction comparison. Its restriction,
followed by the composite-restriction identification, is `sfCompactSupportTransition`.
Source: blueprint order 2135, Proof paragraph 2
(blueprint: lem-coef-integral-compact-support). -/
noncomputable def coefCompactSupportFiniteTransition
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :=
  (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c).map
      (sfCompactSupportReductionTransition l E X K n) ≫
    (sfCompactSupportRestriction c
      (Padic.coefficientExtensionTransition l E (n + 1))).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)

/-- The canonical compact-support coefficient comparison: the tensor/restriction
adjoint of the n-th projection of the specified defining Roos triangle. The adjunction
is the recorded one normalized by the tensor unit on K-flat representatives.
No isomorphism or unrelated map is chosen here.
Source: blueprint order 2135, Proof paragraph 2, counit comparison
(blueprint: lem-coef-integral-compact-support). -/
noncomputable def coefIntegralCompactSupportComparison
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (M : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E Y n).obj M ⟶
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) :=
  ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose.homEquiv M _).symm
    (p ≫ Pi.π _ n)

/-- Integral compact support is constructible, has its prescribed canonical finite
reductions, and has uniform reduction Tor interval [a,b+2d]. The coefficient comparisons
commute with successive quotient reductions. M, p and delta specify the defining
Roos triangle of Rf_!K, rather than an additional assumption on f or K.
Source: blueprint order 2135, lem-coef-integral-compact-support
(blueprint: lem-coef-integral-compact-support).

Proof plan (the nine steps of the DAG node):
1. Integral constructibility supplies constructible reductions. Resolve K by a K-flat
complex P (lem-pc-kflat-resolution); derived change of rings computes its reductions
and their quotient maps (def-weil-integral-derived-reduction, lem-pur-derived-change-of-rings).
2. Tensor reassociation on P identifies every iterated reduction with the direct one.
The balanced maps (x tensor u) tensor v ↦ x tensor uv and their inverses preserve
all quotient cocycles (def-pc-kflat-complex, def-pur-sheaf-tensor-product).
3. For the bound, densely refine c (def-nagata-dense-refinement,
prop-nagata-dense-refinement). The open immersion is quasi-compact by
lemma-nagata-open-immersion-qc-over-separated-target and topologically dense by
lemma-nagata-immersion-open-in-scheme-image. DimensionExtension
(lem-kun-dimension-extension) bounds the new middle scheme's dimension by d.
4. Extension by zero preserves constructibility and [a,b] (lem-trf-open-ctf).
The finite-level direct-image result (cor-sf-direct-image-ctf-proetale) then gives
constructibility and [a,b+2d] for the dense compactification.
5. Constructible pro-etale origin (lem-sf-proetale-constructible-origin) permits
prop-compactification-coherence-detailed to transport this bound back to the original
fixed c. Tensoring isomorphisms preserves the intrinsic all-module Tor test.
6. The actual finite transitions above satisfy the quotient cocycle by
lem-sf-compact-support-restriction-of-scalars. Their adjoints are the canonical tensor
comparisons of lem-fix-compact-support-coefficient-change, hence are isomorphisms.
7. Represent successive transitions by roofs (lem-pc-quasi-isomorphisms-multiplicative-system)
and choose chain maps inductively. Their composites give a strict tower realizing the
specified derived tower, with no additional relations (def-coef-normalized-dvr-tower).
8. Apply lem-coef-normalized-dvr-effectivity to this normalized coherent tower and the
specified Roos triangle. It makes M derived complete, identifies its projection adjuncts
with the displayed isomorphisms, and gives their compatibility with successive reductions.
9. Steps 5 and 8 give constructible reductions with the common Tor interval [a,b+2d].
Testing tensor with the coefficient module itself gives the same cohomological interval.
Together with derived completeness these are precisely sfIntegralConstructible
(def-weil-derived-complete-integral-detailed), proving integral membership.
-/
theorem integralCompactSupport_prescribedReductions
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b : ℤ) (_hab : a ≤ b)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hK : sfIntegralConstructible l E X K)
    (_hTor : ∀ n : ℕ,
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) a b)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n)
    (δ : (∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n) ⟶ M⟦(1 : ℤ)⟧)
    (_hc : IsDerivedLimitTriangle (sfCompactSupportTransition l E c K) M p δ) :
    sfIntegralConstructible l E Y M ∧
      (∀ n : ℕ, IsIso (coefIntegralCompactSupportComparison l E c K M p n)) ∧
      (∀ n : ℕ,
        HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension.{u, u} l E Y n).obj M) a (b + 2 * (d : ℤ))) ∧
      (∀ n : ℕ,
        coefIntegralCompactSupportComparison l E c K M p (n + 1) ≫
            coefCompactSupportFiniteTransition l E c K n =
          sfCompactSupportReductionTransition l E Y M n ≫
            (sfCompactSupportFiniteRestriction l E Y n).mapDerivedCategory.map
              (coefIntegralCompactSupportComparison l E c K M p n)) := by
  sorry

end WeilConjectures
