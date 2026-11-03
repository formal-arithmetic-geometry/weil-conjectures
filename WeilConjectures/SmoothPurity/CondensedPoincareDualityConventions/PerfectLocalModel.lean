/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteLocallyProjective
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.SixFunctors.CondensedPoincareDualityConventions.PerfectLocalModelFlatTor
import WeilConjectures.SmoothPurity.CondensedPoincareDualityConventions.PerfectLocalModelConstructible
import WeilConjectures.SmoothPurity.CondensedPoincareDualityConventions.PerfectLocalModelBounded

/-! # The local finite projective model

Source: latest blueprint, sec-six-functors/sk-def-ops,
prop-pod-perfect-local-model.md and its proof; Stacks Tags 093U and 0GN1.
(blueprint: prop-pod-perfect-local-model).

The hypotheses use local retracts on the small pro-etale site, with varying
finite ranks. The consequence allows both the complex and its degree bounds
to vary over the covering. Finite-stalk constructibility is expressed in the
native condensed constant-model coordinates. The inputs are a finite discrete
commutative ring and a qcqs scheme, so the statement does not depend on the
unpublished Poincare conventions package.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedPoincareDualityConventions

/-- A finite locally projective coefficient module is flat, has degree-zero
Tor amplitude and finite Tor amplitude, and is constructible with finite stalks.
A complex locally represented by bounded complexes of such modules has bounded
constructible cohomology.

Source: latest blueprint, sec-six-functors/sk-def-ops,
prop-pod-perfect-local-model.md; Stacks Tags 093U and 0GN1.
(blueprint: prop-pod-perfect-local-model).

Proof in words, following the reviewed DAG refinement of the blueprint proof:
1. The finite discrete coefficient comparison identifies Lambda_X with the
constant ring sheaf. Locally choose a finite free retract with maps iota and pi.
The idempotent iota pi has image P and P is the kernel of 1 - iota pi.
The locally constant finite-type Serre lemma therefore makes P locally constant
of finite type. Over the finite ring its stalks are finite, so the one-stratum
partition makes it constructible. This is exactly constant-model constructibility
by the finite coefficient model comparison.
2. The finite local-projective retract criterion makes P dualizable. Dualizable
modules are flat, so tensoring with P is exact.
3. Apply the flat single-complex Tor lemma: the derived tensor of P in degree
zero with a module in degree zero is concentrated in degree zero. This gives
Tor amplitude [0,0], and hence finite Tor amplitude.
4. For each local bounded projective complex, use step 1 termwise. Restriction
is exact, so its cohomology sheaves are kernels modulo images of locally constant
finite-type sheaves. The Serre lemma makes these locally constant of finite type;
the local trivializations compose to give constructibility with finite stalks.
5. The scheme X is qcqs by hypothesis. Take a finite affine cover and finite
affine pro-etale refinements of the model covering. The finitely many local intervals have a
common lower
and upper bound. Exact restriction and covering descent of vanishing give zero
global cohomology outside this interval. Step 4 gives constructibility in every
degree. The empty scheme and zero ranks are included throughout. -/
theorem perfect_local_model (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [Finite A]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    let Λ := Profinite.continuousCoefficientRingObj A
    (∀ P : supportModules Λ X, IsFiniteLocallyProjective Λ X P →
      ObjectProperty.flat P ∧
      DerivedCategory.torAmplitudeIn (supportModules Λ X) 0 0
        ((DerivedCategory.singleFunctor (supportModules Λ X) 0).obj P) ∧
      DerivedCategory.finiteTorAmplitude (supportModules Λ X)
        ((DerivedCategory.singleFunctor (supportModules Λ X) 0).obj P) ∧
      IsConstantModelConstructible Λ X P) ∧
    (∀ K : DerivedCategory (supportModules Λ X),
      (∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        ∃ (C : CochainComplex (supportModules Λ (𝒰.X i)) ℤ) (a b : ℤ),
          C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
          (∀ q : ℤ, IsFiniteLocallyProjective Λ (𝒰.X i) (C.X q)) ∧
          Nonempty ((supportPullback Λ (𝒰.f i)).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj C)) →
      constantModelBoundedConstructible Λ X K) := by
  dsimp
  constructor
  · intro P hP
    have hft := perfect_local_model_flat_tor _ X P hP
    have hc := perfect_local_model_constructible A X P hP
    exact ⟨hft.1, hft.2.1, hft.2.2, hc⟩
  · exact perfect_local_model_bounded A X


end WeilConjectures.CondensedPoincareDualityConventions
