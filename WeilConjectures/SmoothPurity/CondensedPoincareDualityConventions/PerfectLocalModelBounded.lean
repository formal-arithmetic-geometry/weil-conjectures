/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteLocallyProjective

/-! # Global bounded constructibility of local finite projective models

A component of the local finite projective model proposition. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedPoincareDualityConventions

/-- Local bounded finite projective models give bounded constructible cohomology.

Source: latest blueprint, sec-six-functors/sk-def-ops,
prop-pod-perfect-local-model.proof.md, cohomology and globalization paragraphs;
Stacks Tags 093U and 0GN1.
(blueprint: lem-pod-perfect-local-model-bounded).

Proof in words. On a member of the given pro-etale cover, every term of its bounded
model is locally a finite free retract. Identify each term locally with the kernel
of one minus a finite-free idempotent. The finite-type locally constant Serre theorem
then applies to its consecutive differentials: kernels, images and cokernels, hence
cohomology, are locally constant of finite type. The coefficient ring is finite,
so the resulting local constant stalk modules are finite. Exact restriction identifies
these sheaves with the restrictions of the cohomology sheaves of K. Composing their
trivializing covers gives constant-model constructibility in every degree on X.
For boundedness, X is qcqs by hypothesis. Choose a finite affine open cover of X.
The finite-refinement clause in the pro-etale covering condition supplies finitely many affine
opens in the model
cover over each affine. Restrict the local models to these opens. There are finitely
many resulting degree intervals; take their common minimum and maximum. Exact
restriction shows that all restricted cohomology sheaves vanish outside this common
interval. A sheaf vanishing on a cover is zero, so the global cohomology vanishes
there too. These global bounds and the preceding constructibility assertions give
the required bounded constructible predicate. For an empty cover X is empty and all
cohomology sheaves are zero; one may choose the interval [0,0]. -/
theorem perfect_local_model_bounded (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [Finite A]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    let Λ := Profinite.continuousCoefficientRingObj A
    ∀ K : DerivedCategory (supportModules Λ X),
      (∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        ∃ (C : CochainComplex (supportModules Λ (𝒰.X i)) ℤ) (a b : ℤ),
          C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
          (∀ q : ℤ, IsFiniteLocallyProjective Λ (𝒰.X i) (C.X q)) ∧
          Nonempty ((supportPullback Λ (𝒰.f i)).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj C)) →
      constantModelBoundedConstructible Λ X K := by
  sorry

end WeilConjectures.CondensedPoincareDualityConventions
