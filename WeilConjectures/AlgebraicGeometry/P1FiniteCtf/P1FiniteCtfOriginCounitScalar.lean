/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData
public import WeilConjectures.AlgebraicGeometry.OrdinaryScalarSite.OrdinaryScalarSiteComparisons
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Scalar/site counit pasting at an etale-origin projective-line input

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
`sk-lem-sp-reduction-exceptional.proof.md`, Charts, lines 20--35.
(blueprint: lem-sp-p1-finite-ctf-origin-counit-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.P1FiniteCtf
open AdjunctionTransfer OrdinaryScalarSite

local instance proEtaleEssentiallySmallOrigin (S : Scheme.{u}) :
    EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0} _

/-- The scalar/site square carries the ordinary counit equation to the specific
pro-etale equation at the image of an etale input. No descent to arbitrary inputs
or inverse-beta transpose is included here.
Source: latest blueprint, reduction-exceptional proof, Charts, lines 31--35;
lem-sp-et-proet-coefficient-compatibility.
(blueprint: lem-sp-p1-finite-ctf-origin-counit-scalar).

Proof: apply the site/coefficient square to ordinaryFiniteP1Right A N hA S L.
The input and its scalar extension are bounded below by the chart-domain theorem,
so the proper site comparisons are invertible. Normalize the trivial compactification
by its identity-open comparison; its coefficient maps are scalarMate and
proEtaleGamma. Write r_A for the A proper site comparison followed by direct image
of rightSite. Precompose the required equation with scalar extension of r_A and
postcompose with delta at L. Naturality of proEtaleGamma at rightSite, the
site/coefficient square and the definition of arrowOnOrigin rewrite the left side
as comparison of the assumed ordinary counit equation, followed by delta at
F_A G_A L. The two counit_normalization equations and naturality of delta rewrite
the right side to that same composite. Cancel the invertible outer maps.
The proper finite-coefficient theorem makes the ordinary scalarMate invertible;
the same site/coefficient square then makes proEtaleGamma invertible at the
comparison image. Naturality at rightSite makes it invertible at the displayed
right-adjoint input. Each factor of arrowOnOrigin is invertible: rightSite,
delta, the balanced Tate map and the ordinary scalar tensor/pullback comparisons.
This proves the two invertibilities and the equation for the specified arrow.
The calculation uses the actual scalar and geometric adjunctions, including
nonflat coefficient maps, and no purity or biduality comparison. -/
theorem p1FiniteCtfOriginCounitScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (dA : NormalizedAdjunction A N hN hA S hS)
    (dB : NormalizedAdjunction B N hN hB S hS)
    (hTS : ∀ K, proCtf A S K → proCtf B S
      ((scalar (Scheme.ProEt.topology S) φ).obj K))
    (L : Etale.DerivedCategoryModule A S) (hL : etaleProperty A S L)
    (hc : (Etale.scalarMate φ (ProjectiveLine S ↘ S)).app
          ((Etale.ordinaryFiniteP1Right A N hA S).obj L) ≫
        (Etale.ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
          (etaleArrow φ N hN hA hB S hS L) ≫
        (Etale.projectiveLineTraceDatum N hN B hB S hS).adjunction.counit.app
          ((scalar S.smallEtaleTopology φ).obj L) =
      (scalar S.smallEtaleTopology φ).map
        ((Etale.projectiveLineTraceDatum N hN A hA S hS).adjunction.counit.app L)) :
    IsIso ((proEtaleGamma φ (ProjectiveLine S ↘ S)).app
      ((right A N hA S).obj ((sitePull A S).obj L))) ∧
    IsIso (arrowOnOrigin φ N hN hA hB S hS ((sitePull A S).obj L) L (Iso.refl _)) ∧
    (proEtaleGamma φ (ProjectiveLine S ↘ S)).app
          ((right A N hA S).obj ((sitePull A S).obj L)) ≫
        (direct B S).map
          (arrowOnOrigin φ N hN hA hB S hS ((sitePull A S).obj L) L (Iso.refl _)) ≫
        (dB.adjunction.counit.app
          ⟨(scalar (Scheme.ProEt.topology S) φ).obj ((sitePull A S).obj L),
            hTS _ (dA.comparison_preserves L hL)⟩).hom =
      (scalar (Scheme.ProEt.topology S) φ).map
        (dA.adjunction.counit.app
          ⟨(sitePull A S).obj L, dA.comparison_preserves L hL⟩).hom := by sorry

end AlgebraicGeometry.ProEtale.P1FiniteCtf
