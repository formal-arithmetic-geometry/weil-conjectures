/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.DualityPairing
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # Proper pushforward and ambient biduality

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-weil-delta-proper-pushforward.md and its proof
(blueprint: lem-weil-delta-proper-pushforward).

The equation uses the existing ambient Verdier exchange, in the direction
`χ_K : Rf_* D_X K ⟶ D_Y Rf_* K`. It reads
`Rf_* δ_K ≫ χ_{D_X K} = δ_{Rf_* K} ≫ D_Y(χ_K)`.
Since both exchange components are invertible, this is exactly identification by
`χ_{D_X K} ≫ D_Y(χ_K)⁻¹`. All complexes are unbounded ambient objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The dualizing comparison obtained by conjugating the graph-normalized compact-support
compositor by the specified exceptional adjunctions, evaluated at the coefficient unit.
Source: blueprint lem-weil-delta-proper-pushforward.proof.md, first paragraph
(blueprint: lem-weil-delta-proper-pushforward). -/
noncomputable def properPushforwardDualizingIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ S)
    [HasCompactification f] [HasCompactification aY] [HasCompactification (f ≫ aY)] :
    (R(f)^![Λ]).obj (dualizingComplex Λ aY) ≅ dualizingComplex Λ (f ≫ aY) :=
  ((((rightDerivedUpperShriekAdjunction Λ (f ≫ aY)).ofNatIsoLeft
    (sfGraphCompactSupportCompIso Λ f aY
      (HasCompactification.compactification f) (HasCompactification.compactification aY)
      (HasCompactification.compactification (f ≫ aY)))).rightAdjointUniq
        ((rightDerivedUpperShriekAdjunction Λ f).comp
          (rightDerivedUpperShriekAdjunction Λ aY))).app (𝟙_ _)).symm

/-- The ambient exchange with its specified graph-composition dualizing comparison.
Source: blueprint lem-weil-delta-proper-pushforward.proof.md, first two paragraphs
(blueprint: lem-weil-delta-proper-pushforward). -/
noncomputable def ambientProperVerdierExchange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y S : Scheme.{u}} (aY : Y ⟶ S) (f : X ⟶ Y) [IsProper f]
    [HasCompactification f] [HasCompactification aY] [HasCompactification (f ≫ aY)] :
    (R((f)_*[ModuleCat.{u + 1} Λ])) ⋙ (verdierDual Λ aY).rightOp ≅
      (verdierDual Λ (f ≫ aY)).rightOp ⋙ (R((f)_*[ModuleCat.{u + 1} Λ])).op :=
  verdierDualLowerShriekIso (ModuleCat.{u + 1} Λ) f
    (dualizingComplex Λ aY) (dualizingComplex Λ (f ≫ aY))
    (derivedHomRightDerivedLowerShriekIsoOfFinite Λ f)
    (properPushforwardDualizingIso Λ f aY)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f)

/-- Proper pushforward identifies the ambient double-dual arrows through the canonical
Verdier exchange, and hence preserves the asserted invertibility of the double-dual arrow.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-weil-delta-proper-pushforward.md
(blueprint: lem-weil-delta-proper-pushforward).

Proof:
1. Finite-type schemes over the field are Noetherian (lem-wf-affine-noetherian-components).
Nagata compactification and the proper shriek/star comparison identify compact supports for
f with Rf_*. Compose the ambient exceptional adjunctions, using compact-support composition
(lem-etale-unbounded-compact-support-composition), composite adjunction and adjunction
conjugation. This identifies ω_X with f^×ω_Y and gives the counit trace Rf_*ω_X → ω_Y.
2. The derived categories are locally small and closed symmetric monoidal
(lem-pc-derived-category-locally-small, lem-sf-ringed-derived-closed-symmetric-monoidal).
The inverse image is strong symmetric monoidal and direct image has its adjoint lax symmetric
structure (lem-pur-etale-derived-direct-image-lax-symmetry). Transpose pushed-forward
evaluation followed by the trace to obtain χ. The unbounded proper projection formula
(lem-amb-proper-coproducts-projection) and lem-pur-projection-dual-comparison make χ invertible.
Its adjunction chain is the ambient exchange of prop-asd-internal-adjunction.
3. Apply lem-pur-lax-symmetric-bidual-square to the lax symmetric direct image and trace.
It gives the displayed equation. Both exchange components, and the dual of the first,
are invertible. Cancel the latter to identify the double-dual arrows. If δ_{Rf_*K} is
invertible, the equation expresses Rf_*δ_K as a composite of isomorphisms. No constructible
admissibility or geometric biduality enters this argument. -/
theorem ambient_delta_proper_pushforward
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) [IsProper f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((R((f)_*[ModuleCat.{u + 1} Λ])).map
        ((verdierDualDoubleDual Λ (f ≫ aY)).app K) ≫
      ((ambientProperVerdierExchange Λ aY f).hom.app
        ((verdierDual Λ (f ≫ aY)).obj (op K))).unop =
      (verdierDualDoubleDual Λ aY).app ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (verdierDual Λ aY).map
          ((ambientProperVerdierExchange Λ aY f).hom.app K)) ∧
    (IsIso ((verdierDualDoubleDual Λ aY).app
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K)) →
      IsIso ((R((f)_*[ModuleCat.{u + 1} Λ])).map
        ((verdierDualDoubleDual Λ (f ≫ aY)).app K))) := by
  sorry

end AlgebraicGeometry.Etale
