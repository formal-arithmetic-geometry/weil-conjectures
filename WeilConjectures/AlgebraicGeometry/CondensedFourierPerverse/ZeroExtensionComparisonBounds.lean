/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierPerverse.CondensedFourierPerverse
public import WeilConjectures.AlgebraicGeometry.AffineLineConventions.AffineLineConventions
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.CondensedFourierKernel
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedRealified.CondensedRealifiedKernel
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedOpenClosedLocalizationMapsCore
public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.ConstituentNonexceptional

/-! # Lissity and weights of zero-extension corrections

The corresponding component of the blueprint zero-extension comparison proof. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedFourierPerverse

open CondensedCurvePerverse
open AffineLineConventions
open CondensedGenericWeil
open WeilConjectures
open WeilConjectures.NativeL2
open WeilConjectures.CondensedRealified
open WeilConjectures.CondensedWeil

/-- Lissity and weight bounds for every structural zero-extension correction.

Source: `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/`
`sk-p-dl-a1-correction/prop-fd-zero-extension-comparison.proof.md`, Steps 3 and 4.

Proof in words: The canonical boundary map in C has cokernel equal to the finite sum of
closed-point boundary stalks E_s. Closed base change and the projection formula compute
its Fourier transform as B'[1], where B' is the sum of the finite-etale direct images
of E_s pulled back and tensored with the Artin--Schreier sheaf of s times xi. Comparing
with C.isoBoundary and using full faithfulness of the shifted single functor identifies
C.seq.X1 with B' as a Weil module. The canonical mate condition ensures that this uses
the same open extension and boundary morphism as C.

Each tensor factor is lisse, and finite-etale direct image and finite sums preserve
lissity. For weights, boundary semicontinuity bounds each eigenvalue mu of Frobenius on
E_s by squared modulus q_s^w. At a point z of degree n above s, pullback Frobenius acts
by the n/d(s) power. The Artin--Schreier rank-one factor has Frobenius eigenvalue a root
of unity, hence modulus one. Tensoring gives the bound q^(wn) at z.

At a closed point y on the dual line, finite-etale direct image decomposes its geometric
stalk into summands permuted by Frobenius. On an orbit of length e, the e-th power of
Frobenius acts as the local Frobenius at a point z of degree e*d(y). If alpha is an
eigenvalue, select a nonzero component of an eigenvector in such an orbit. Its eigenvalue
for this power is alpha^e, giving modulus squared at most q^(w*e*d(y)). Taking the
positive e-th root gives squared modulus at most q_y^w. Finite sums preserve the bound;
transport it along the Weil isomorphism to C.seq.X1 and take square roots to obtain the
norm formulation HasClosedOperatorWeightsAtMost. In the empty-complement case B' is
zero, so lissity holds and there are no eigenvalues to check.
(blueprint: prop-fd-zero-extension-comparison-bounds) -/
theorem zeroExtensionComparison_bounds
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hℓ : l ≠ D.p)
    (ψ : AddChar D.k₀ (MonObj.Γ (Profinite.padicAlgClRingObj l))) (hψ : ψ ≠ 1)
    {U₀ U₁ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType U₁.hom] [QuasiCompact U₁.hom]
    (j₀ : U₀ ⟶ lineModel D) (j₁ : U₁ ⟶ lineModel D)
    [IsOpenImmersion j₀.left] [IsOpenImmersion j₁.left]
    [IsOpenImmersion (NativeL2.geometricMap D j₀)]
    [IsDominant j₀.left] [IsDominant j₁.left]
    (M : Lisse l (D.geometricFrobenius U₀))
    (hM0 : ¬ IsZero M.obj.carrier)
    (hMsimple : Simple M)
    (hne : IsConstituentNonexceptional D U₀ l j₀ M ψ)
    (M' : Lisse l (D.geometricFrobenius U₁))
    (c : Compactification (secondModel D).left)
    (hFT : Nonempty (Endofunctor.IsoAlgebra.mk
          ((transform D l ψ c).obj
            (shiftedSingle D l
              (NativeL2.middleWeilImage D l j₀ M.obj).carrier))
          (frobeniusComponent D l ψ c _ ≪≫
            (transform D l ψ c).mapIso
              (shiftedWeilSingle D l (NativeL2.middleWeilImage D l j₀ M.obj)).str) ≅
        shiftedWeilSingle D l (NativeL2.middleWeilImage D l j₁ M'.obj)))
    (ι : PadicAlgCl l →+* ℂ) {w : ℝ}
    (hw : NativeL2.Pure D l U₀ M.obj ι w)
    (C : CondensedFourierCorrection D l j₀ j₁ M M' ψ c) (_hC : C.seq.ShortExact) :
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) C.seq.X₁.carrier ∧
      HasClosedOperatorWeightsAtMost D l C.seq.X₁ ι w := by
  sorry


end AlgebraicGeometry.ProEtale.CondensedFourierPerverse
