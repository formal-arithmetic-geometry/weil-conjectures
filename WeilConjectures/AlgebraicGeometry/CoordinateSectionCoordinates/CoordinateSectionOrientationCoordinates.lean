/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionCoordinates.CoordinateSectionTateCoordinates

/-! # The actual coordinate orientation in ordinary coordinates

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, rank-one calculation and
finite etale-origin transport (blueprint: lem-pur-coordinate-section-orientation-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.CoordinateSectionCoordinates
open AffineZeroPurity AffineSpacePurity AffineLinePurity VectorIntegrationSite
open CoordinateSectionNormalization

/-- The actual Cartier adjunct agrees with the ordinary rank-one orientation
under the specified source and exceptional-target identifications.

Source: current blueprint, rank-one Cartier calculation, even-twist paragraph
and finite-site transport sentence
(blueprint: lem-pur-coordinate-section-orientation-coordinates).

Proof: the CartierRealization clause of twistedCoordinateSectionNormalization
identifies the ordinary supported Cartier map with the published coordinate
boundary. At rank one the supported cup product is this arrow followed by the
canonical coefficient unitor. Tensor it with the r-th Tate input and transport
through tensorComparison and tateComparison. Naturality of the proper closed
projection formula identifies its inverse with sectionProjection; the two tensor
symmetries give exactly sectionTargetIso, since all shifts are even. The resulting
supported arrow is sectionArrow by its defining uniqueness theorem. Apply the
closed Hom bijections to this equality. The counit equation for uniqueness of
right adjoints gives ordinaryClosedComparison; exact site comparison and the
bounded comparison unit give proOrientation. Naturality of transposition in
both endpoints gives the displayed square. No orientation is chosen, and no
invertibility of sectionAdjunct is used. For r=0 the coefficient unitors are the
specified identity normalization; over the empty scheme all maps are zero. -/
theorem sectionAdjunct_coordinates
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ)
    (hI : (sectionMap (iteratedAffineLine B r)).ker.IsInvertible)
    (hT : IsUnit ((P.coefficients.l ^ ((setting P n).level + 1) : ℕ) :
      Γ(iteratedAffineLine B r, ⊤)))
    (hpf : IsIso (closedProjection (setting P n).Coefficient (iteratedAffineLine B r)
      (input P n (iteratedAffineLine B r) r))) :
    sectionAdjunct P n B aB r ≫ (orientationTargetComparison P n B aB r).hom =
      (tateComparison P n (iteratedAffineLine B r) (towerBase aB r) r).inv ≫
        proOrientation (iteratedAffineLine B r) (setting P n) (setting P n).level
          (annihilates (setting P n)) hT hI (input P n (iteratedAffineLine B r) r) hpf := by
  sorry

end AlgebraicGeometry.ProEtale.CoordinateSectionCoordinates
