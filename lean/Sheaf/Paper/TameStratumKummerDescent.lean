/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerStratumChart
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.CategoryTheory.CondensedDerivedInvariantBar
import Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization
import Sheaf.Paper.RingedDerivedSliceLocalization
import Sheaf.RepresentationTheory.PrimeToEllLinearImageFinite
import Sheaf.CategoryTheory.DerivedCechImageTotalization
import Sheaf.Paper.RootTowerBoundaryAcyclicity
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-! # Kummer descent on entire normal-crossing strata
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3).
(blueprint: lem-sfb-tame-stratum-kummer-descent).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale
open CategoryTheory.CondensedBar

/-- The whole-stratum assertion uses the canonical open complement and reduced SNC
stratum, retaining empty strata and empty index. The existence of the action-category
structures and normalized bar models is included in the conclusion, so no categorical
existence hypothesis is added to the geometric input.
Source: direct-image proof (3), complete tame-boundary calculation
(blueprint: lem-sfb-tame-stratum-kummer-descent). -/
def TameStratumKummerAssertion (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {Y : Scheme.{u}}
    (D : Y.IdealSheafData) (hD : IsStrictNormalCrossingsBoundary D)
    (L : KummerModules (Profinite.continuousMapRingObj E.1) (tameBoundaryOpen D).toScheme)
    (I : Finset (Fin hD.2.2.choose)) : Prop := by
  let C := kummerComponents D hD
  let K := kummerIndices D hD I
  let G := kummerChartGroup p K
  refine ∃ h : ∀ R : Ring.{u}, ActionAbelian R G, ?_
  letI (R : Ring.{u}) : ActionAbelian R G := h R
  refine ∃ g : ∀ R : Ring.{u}, IsGrothendieckAbelian.{u + 1} (Equivariant R G), ?_
  letI (R : Ring.{u}) : IsGrothendieckAbelian.{u + 1} (Equivariant R G) := g R
  letI (R : Ring.{u}) : HasDerivedCategory.{u + 2} (Equivariant R G) :=
    HasDerivedCategory.standard (Equivariant R G)
  letI (R : Ring.{u}) : HasDerivedCategory.{u + 2} (Modules R) :=
    HasDerivedCategory.standard (Modules R)
  exact ∃ models : ∀ R : Ring.{u}, Model R G,
    ∃ b : ScalarModel (kummerCoefficientMap ℓ E)
      (models (kummerCoefficientRing.{u} E.1))
      (models (kummerCoefficientRing.{u} (PadicAlgCl ℓ))),
      Nonempty (ScalarComputation (kummerCoefficientMap ℓ E) b) ∧
      ∃ B : Scheme.Cover.{u} Scheme.proetalePrecoverage (ParameterStratum C K),
        ∀ α : B.I₀, ∃ (c : TameRootExtensionChart C K) (e : B.X α ≅ c.boundary),
          e.hom ≫ c.boundaryToStratum = B.f α ∧
          ∃ geometry : TameRootChartGeometry p D c,
            Nonempty (KummerStratumChart p ℓ E D C K L c
              (models (kummerCoefficientRing.{u} E.1))
              (models (kummerCoefficientRing.{u} (PadicAlgCl ℓ))) b geometry)

/-- A common pro-etale cover gives normalized ordinary derived Kummer descent over
both E and its norm-topological algebraic closure. The assertion is about derived
module sheaves on entire reduced strata, with the actual augmented nerve, continuous
parameter action, direct-image counit, scalar unit, and restriction maps retained.
Source: direct-image proof (3), agent-formulated tame-boundary calculation
(blueprint: lem-sfb-tame-stratum-kummer-descent).

Proof:
1. Apply `lem-sfb-tame-root-tower-extension` to obtain a common cover, compatible
root characters, full-root charts and the boundary representations. Root ratios give
successive group coordinates on the actual punctured Cech nerve; multiplying the
first lift by cumulative coordinates gives the inverse.
2. The subgroup H_I has only finite quotients of order prime to ell. Apply
`lem-sfb-prime-to-ell-linear-image-finite` to get the required finite image.
3. Use `def-sfb-lisse-coefficient-module` and `sk-def-sfb-pulled-back-coefficients`
to extend the E model by the ordinary tensor to Omega. A finite E basis identifies
both condensations and the coefficient unit, so the cover and representation agree.
4. Localize before restricting to the boundary, using
`lem-sfb-coefficient-sections-localization` and
`lem-weil-pbc-ringed-derived-slice-localization`, preserving the actual counit.
Then `lem-sfb-derived-cech-image-totalization` computes the source by the augmented
punctured nerve on nonnegative resolutions, whose total has finite diagonals.
5. Apply `lem-sfb-root-tower-boundary-acyclicity` to every profinite parameter
G_I^n. Its inverse-puncture-unit and actual-counit-mate normalization identifies each
column with the existing universal derived evaluation. Parameter naturality gives
all faces and degeneracies; the first face is the representation action.
6. Apply `lem-sfb-condensed-derived-invariant-bar` to the coherent diagram. Exact
point inverse image commutes with its finite-diagonal total. Its invariant
augmentation fixes the degree-zero restriction map.
7. Use `lem-weil-pbc-ring-sheaf-change-adjunction` on the actual coefficient unit
in every nerve degree. The scalar adjunction mate preserves the counit and both
augmentations, so the total gives the required coefficient square after restriction
of scalars. The naturality clauses of `lem-sfb-derived-cech-image-totalization`,
`lem-sfb-root-tower-boundary-acyclicity` and
`lem-sfb-condensed-derived-invariant-bar` restrict this same normalized descent to
every morphism into a covering member, as required by `KummerRefinementNatural`.
8. For empty I the identity root tower and trivial group from
`lem-sfb-tame-root-tower-extension` give a pro-etale trivialization; the same ordinary
scalar extension gives Omega. Zero rank and empty strata give the zero model and
empty cover. -/
theorem tameStratumKummerDescent
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (_hY : IsRegularScheme Y)
    (D : Y.IdealSheafData) (hD : IsStrictNormalCrossingsBoundary D)
    (L : KummerModules (Profinite.continuousMapRingObj E.1) (tameBoundaryOpen D).toScheme)
    (_hL : IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) L)
    (_htame : IsStrictLocalKummerTameModule p (Profinite.continuousMapRingObj E.1)
      D (tameBoundaryOpen D).ι L) (I : Finset (Fin hD.2.2.choose)) :
    TameStratumKummerAssertion p ℓ E D hD L I := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
