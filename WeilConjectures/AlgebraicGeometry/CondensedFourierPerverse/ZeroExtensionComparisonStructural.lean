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

/-! # Structural zero-extension correction

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

/-- Structural part of the zero-extension comparison.

Source: `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/`
`sk-p-dl-a1-correction/prop-fd-zero-extension-comparison.proof.md`, Steps 1, 2 and 5.

Proof in words: Apply open--closed localization to the middle extension. Its restriction
back to the open is M, so the canonical map from the open extension is injective and its
cokernel is supported on the finite complement. Decompose that cokernel into the direct
sum of its closed-point boundary stalks E_s. Construct the open Frobenius comparison as
the inverse of the adjoint mate of the Frobenius square; naturality makes the canonical
open-to-middle map a Weil morphism with the required underlying map.

For each boundary point, closed base change and the projection formula identify the
Fourier transform with the finite direct image of the pullback of E_s tensored with the
rank-one Artin--Schreier sheaf for the linear function s times xi, shifted by one.
Finite-etale direct image is exact, so additivity gives the boundary comparison with
a degree-one shifted sheaf B'. These comparisons commute with Frobenius.

Apply the geometric Fourier functor to the localization triangle and rotate it. The
Fourier-partner hypothesis identifies the third term with the shifted middle extension
of M'. Both outer terms have cohomology only in degree minus one, so the geometric heart
long exact sequence gives the short exact sequence from B' through H^(-1) of the
transformed open extension to the middle extension of M'. Truncation identifies the
middle complex with that shifted cohomology sheaf. Transport Frobenius through these
canonical isomorphisms and assemble the correction package. No triangulated structure
on the category of Weil pairs is used: triangles and truncations are geometric.
(blueprint: prop-fd-zero-extension-comparison-structural) -/
theorem zeroExtensionComparison_structural
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
    (hw : NativeL2.Pure D l U₀ M.obj ι w) :
    ∃ C : CondensedFourierCorrection D l j₀ j₁ M M' ψ c, C.seq.ShortExact := by
  sorry


end AlgebraicGeometry.ProEtale.CondensedFourierPerverse
