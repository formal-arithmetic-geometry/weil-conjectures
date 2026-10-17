/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Adic

/-!
# Smooth purity with coefficients in `E`

At the stage `Λ = E`, a finite extension of `ℚ_ℓ`, an object is presented by a lattice: an
object of the integral stage `D_comp(X, 𝒪_E)` (`DerivedCategoryDerivedCompleteIntegral`),
viewed in its rationalization `D_comp(X, E)` (`DerivedCategoryDerivedCompleteRational`) through
the localization functor `fromIntegral`, the exact functor `- ⊗ᴸ_{𝒪_E} E`. The `E`-purity
isomorphism is the image of the adic purity isomorphism of
`AlgebraicGeometry.Etale.exists_iso_realization_twistShiftPullbackLevel` under this functor
(blueprint `thm-pur-rational-and-qbar-purity`, Step 1).

## Main statements

- `AlgebraicGeometry.Etale.exists_iso_fromIntegral_realization_twistShiftPullbackLevel`
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E]
  [∀ n : ℕ, Finite (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
    PadicAlgCl.maximalIdealShrink l E ^ (n + 1))]
  [∀ n : ℕ, HasTateTwist (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
    PadicAlgCl.maximalIdealShrink l E ^ (n + 1))]
  {X Y : Scheme.{u}} (d : ℤ) (f : X ⟶ Y) [HasCompactification f]

/-- Blueprint `thm-pur-rational-and-qbar-purity`: Rational and `ℚ̄_ℓ` purity (`E`-stage
packaging only)

Let `K = (K_n)_n` be a normalized system over `𝒪_E` on `Y`, `S`, `T` normalized systems on `X`
with levels identified with `Lf^* K_n(d)[2d]` and `Rf^! K_n`, and `γ_n` isomorphisms between
these levels forming a morphism of normalized systems (`hγ`). Then any homotopy limits of `S`
and `T` are derived complete, so they are objects of `D_comp(X, 𝒪_E)`; the isomorphism `e`
between them of `AlgebraicGeometry.Etale.exists_iso_realization_twistShiftPullbackLevel`
reduces to `γ_n` at every level, and its image under the exact functor `- ⊗ᴸ_{𝒪_E} E`
(`DerivedCategoryDerivedCompleteRational.fromIntegral`) is an isomorphism in `D_comp(X, E)`.

This is the `E`-stage packaging of the realized isomorphism, not the `E`-part of the
blueprint statement: `hγ` is assumed, the objects are arbitrary homotopy limits rather than
`Lf^* K_E(d)[2d]` and `Rf^! K_E`, and the `IsIso` conclusion follows formally from `e` being an
isomorphism. -/
theorem exists_iso_fromIntegral_realization_twistShiftPullbackLevel
    (K : NormalizedTower (PadicAlgCl.maximalIdealShrink l E) Y)
    (S T : NormalizedTower (PadicAlgCl.maximalIdealShrink l E) X)
    (eS : ∀ n : ℕ, S.obj n ≅ twistShiftPullbackLevel d f K n)
    (eT : ∀ n : ℕ, T.obj n ≅ upperShriekLevel f K n)
    (γ : ∀ n : ℕ, twistShiftPullbackLevel d f K n ≅ upperShriekLevel f K n)
    (hγ : ∀ n : ℕ, S.map n ≫ (derivedRestrictScalars (quotientPowSuccFactor _ n) X).map
        (eS n ≪≫ γ n ≪≫ (eT n).symm).hom =
      (eS (n + 1) ≪≫ γ (n + 1) ≪≫ (eT (n + 1)).symm).hom ≫ T.map n)
    {cS : Cone S.restrict} (hcS : Pretriangulated.IsHomotopyLimit cS)
    {cT : Cone T.restrict} (hcT : Pretriangulated.IsHomotopyLimit cT) :
    ∃ (hS : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E cS.pt)
      (hT : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E cT.pt)
      (e : cS.pt ≅ cT.pt),
      (∀ n : ℕ, e.hom ≫ cT.π.app (Opposite.op n) =
        cS.π.app (Opposite.op n) ≫
          (derivedRestrictScalars (Ideal.Quotient.mk (PadicAlgCl.maximalIdealShrink l E ^ (n + 1)))
            X).map (eS n ≪≫ γ n ≪≫ (eT n).symm).hom) ∧
      IsIso ((DerivedCategoryDerivedCompleteRational.fromIntegral X.smallEtaleTopology l E).map
        (X := ⟨cS.pt, hS⟩) (Y := ⟨cT.pt, hT⟩) (ObjectProperty.homMk e.hom)) := by
  obtain ⟨ϖ, hϖ, hI⟩ := PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  obtain ⟨e, he⟩ := exists_iso_realization_twistShiftPullbackLevel d f K S T eS eT γ hγ hcS hcT
  refine ⟨S.derivedComplete_of_isHomotopyLimit hϖ hI hcS,
    T.derivedComplete_of_isHomotopyLimit hϖ hI hcT, e, he, ?_⟩
  have : IsIso (ObjectProperty.homMk (P := DerivedCategory.derivedCompleteIntegral
      X.smallEtaleTopology l E) (X := ⟨cS.pt, S.derivedComplete_of_isHomotopyLimit hϖ hI hcS⟩)
      (Y := ⟨cT.pt, T.derivedComplete_of_isHomotopyLimit hϖ hI hcT⟩) e.hom) :=
    ⟨ObjectProperty.homMk e.inv, by ext; exact e.hom_inv_id, by ext; exact e.inv_hom_id⟩
  exact Functor.map_isIso _ _

section TraceCoherence

variable {CX CY DX DY : Type*} [Category* CX] [Category* CY] [Category* DX] [Category* DY]
  {L : CX ⥤ CY} {R H : CY ⥤ CX} {L' : DX ⥤ DY} {R' H' : DY ⥤ DX}

/-- Blueprint `prop-pur-rational-purity-trace-coherence`: Trace and coherence compatibilities of
rational purity

Let `Rf_! = L ⊣ R = Rf^!` be the exceptional adjunction at the integral stage and
`L' ⊣ R'` the one at the rational stage, `H = Lf^*(-)(d)[2d]` and `H'` the twisted pullbacks,
and `γ : H ≅ R`, `γ' : H' ≅ R'` the purity isomorphisms, so that the smooth traces are
`Tr^sm_K = ε_K ∘ L(γ_K)` and `Tr'^sm_K = ε'_K ∘ L'(γ'_K)` (`def-pur-smooth-trace`). Let `Φ` be
the exact functor `- ⊗ᴸ_{𝒪_E} E` (or the extension of coefficient fields), commuting with `Rf_!`
(`ψ`), with `Rf^!` (`vS`, compatible with the counits: `hS`) and with the twisted pullbacks
(`v₀`), and suppose the rational purity isomorphism is the transport of the integral one
(`hγ`, `thm-pur-rational-and-qbar-purity`). Then

1. the rational smooth trace is the transport of the integral smooth trace:
   `Φ(Tr^sm_K) = Tr'^sm_{Φ K} ∘ L'(v₀) ∘ ψ`;
2. the trace of a direct summand `N` of `Φ K` (with `i : N ⟶ Φ K`, `r : Φ K ⟶ N`,
   `i ≫ r = 𝟙`) is the summand of the trace: `Tr'^sm_N = r ∘ Tr'^sm_{Φ K} ∘ L'(H'(i))`, by
   naturality of `γ'`.

The composition and base-change coherence squares at the rational stage are, likewise, the
images under `Φ` of the integral ones (`AlgebraicGeometry.Etale.smoothPurityTrace_comp` and
`AlgebraicGeometry.Etale.smoothPurityTrace_baseChange` at the finite levels, realized by
`prop-pur-adic-reconstruction-trace-coherence`), restricted to summands as in (2). -/
theorem map_comp_counit_eq_of_transport (adj : L ⊣ R) (adj' : L' ⊣ R') (ΦX : CX ⥤ DX)
    (ΦY : CY ⥤ DY) (ψ : L ⋙ ΦY ≅ ΦX ⋙ L') (γ : H ≅ R) (γ' : H' ≅ R')
    (vS : R ⋙ ΦX ≅ ΦY ⋙ R') (v₀ : H ⋙ ΦX ≅ ΦY ⋙ H')
    (hS : ∀ K : CY, L'.map (vS.hom.app K) ≫ adj'.counit.app (ΦY.obj K) =
      ψ.inv.app (R.obj K) ≫ ΦY.map (adj.counit.app K))
    (hγ : ∀ K : CY, ΦX.map (γ.hom.app K) ≫ vS.hom.app K = v₀.hom.app K ≫ γ'.hom.app (ΦY.obj K)) :
    (∀ K : CY, ΦY.map (L.map (γ.hom.app K) ≫ adj.counit.app K) =
      ψ.hom.app (H.obj K) ≫ L'.map (v₀.hom.app K) ≫
        L'.map (γ'.hom.app (ΦY.obj K)) ≫ adj'.counit.app (ΦY.obj K)) ∧
    ∀ (K : CY) (N : DY) (i : N ⟶ ΦY.obj K) (r : ΦY.obj K ⟶ N), i ≫ r = 𝟙 N →
      L'.map (γ'.hom.app N) ≫ adj'.counit.app N =
        L'.map (H'.map i) ≫ (L'.map (γ'.hom.app (ΦY.obj K)) ≫ adj'.counit.app (ΦY.obj K)) ≫ r := by
  refine ⟨fun K ↦ ?_, fun K N i r hir ↦ ?_⟩
  · have hψ := ψ.hom.naturality (γ.hom.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at hψ
    rw [← L'.map_comp_assoc, ← hγ K, L'.map_comp_assoc, hS K, ← reassoc_of% hψ,
      Iso.hom_inv_id_app_assoc, Functor.map_comp]
  · simp only [Category.assoc]
    rw [← L'.map_comp_assoc, γ'.hom.naturality i, L'.map_comp_assoc]
    have h₂ := adj'.counit.naturality i
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₂
    rw [reassoc_of% h₂, hir, Category.comp_id]

end TraceCoherence

end Etale

end AlgebraicGeometry
