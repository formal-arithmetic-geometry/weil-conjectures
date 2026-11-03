/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalChosenRestriction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalFactorsRestriction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Affine-local form of finite diagonal orientation assembly

(blueprint: lem-pur-finite-diagonal-orientation-assembly-local).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

variable (P : PurityFiniteSetting.{u})
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The specified three-factor diagonal composite agrees with the chosen orientation
on an affine source cover. This is the local chart calculation used before descent.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, proof Steps 3--4;
lem-pur-diagonal-dnc-chart-normalization and the affine refinement equations.
Proof: choose finite-type affine target opens and affine etale smooth-coordinate
neighbourhoods in their inverse images. Restrict alpha, delta and beta through the
canonical source, normal-cone and Tate comparison maps. The affine normalization
identity identifies the restricted composite with the restricted chosen orientation.
The construction includes the empty cover and rank-zero case. This helper is
strictly local: it asserts equality only after restriction to each member of a
cover, and therefore does not itself prove the global theorem.
(blueprint: lem-pur-finite-diagonal-orientation-assembly-local). -/
theorem diagonalOrientationAssembly_affineLocal :
    ∃ (I : Type u) (U : I → X.Opens),
      iSup U = ⊤ ∧
      ∀ i,
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (U i).ι).mapDerivedCategory.map
          (P.diagonalDualizingObject d f aY).hom =
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (U i).ι).mapDerivedCategory.map
          ((P.chartDiagonalAlpha d f aY).inv ≫
            (P.chartDiagonalDelta d f aY).hom ≫ (vectorFactor P d f aY).hom) := by
  classical
  have cover (x : X) : ∃ (U : X.affineOpens) (V : Y.affineOpens)
      (hUV : U.1 ≤ f ⁻¹ᵁ V.1), x ∈ U.1 ∧
        SmoothOfRelativeDimension d (f.resLE V.1 U.1 hUV) := by
    obtain ⟨V, U, hV, hU, _, hx, hUV, e, he, hw⟩ :=
      Smooth.exists_etale_to_affineSpace f d x
    let : Etale e := he
    have hd : SmoothOfRelativeDimension (0 + d)
        (e ≫ (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme)) := by
      have hp : SmoothOfRelativeDimension d
          (AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme) := by
        simpa only [Nat.card_ulift, Nat.card_fin] using
          (AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) V.toScheme)
      infer_instance
    refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hUV, hx, ?_⟩
    simpa only [Nat.zero_add, hw] using hd
  choose U V hUV hx hd using cover
  refine ⟨X, fun x ↦ (U x).1, ?_, ?_⟩
  · apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    let : IsAffine (U x).1.toScheme := (U x).2
    let : IsAffine (V x).1.toScheme := (V x).2
    let := hd x
    have ha := diagonalChosenRestriction P d f aY (U x) (V x) (hUV x)
    have hb := diagonalFactorsRestriction P d f aY (U x) (V x) (hUV x)
    let t := Etale.projectiveLineTraceTransport P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level)
      P.Coefficient P.diagonalExponent_annihilates
    have hn : (P.diagonalDualizingObject d
        (f.resLE (V x).1 (U x).1 (hUV x)) ((V x).1.ι ≫ aY)).hom =
        (P.chartDiagonalAlpha d (f.resLE (V x).1 (U x).1 (hUV x))
          ((V x).1.ι ≫ aY)).inv ≫
        (P.chartDiagonalDelta d (f.resLE (V x).1 (U x).1 (hUV x))
          ((V x).1.ι ≫ aY)).hom ≫
        (vectorFactor P d (f.resLE (V x).1 (U x).1 (hUV x))
          ((V x).1.ι ≫ aY)).hom := by
      simpa only [chartDiagonalAssembly, vectorFactor, Iso.trans_hom, Iso.symm_hom] using
        congrArg Iso.hom
          (P.diagonal_dnc_chart_normalization d (f.resLE (V x).1 (U x).1 (hUV x))
            ((V x).1.ι ≫ aY) t)
    dsimp only at ha hb
    have he := ha.trans ((congrArg (fun z ↦
      (affineDualizingRestriction P f aY (U x) (V x) (hUV x)).hom ≫ z) hn).trans
        (by simpa only [Category.assoc] using hb.symm))
    have hl := (cancel_mono (affineTateRestriction P f aY d (U x)).hom).1 he
    let c := ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) (U x).1.ι
    exact (NatIso.naturality_1 c _).symm.trans
      ((congrArg (fun z ↦ c.inv.app _ ≫ z ≫ c.hom.app _) hl).trans
        (NatIso.naturality_1 c _))

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
