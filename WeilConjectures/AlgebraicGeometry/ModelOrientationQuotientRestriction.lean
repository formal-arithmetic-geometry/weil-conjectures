/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionModelOrientationDefinitions

/-! # Open restriction of the composition-orientation quotient -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The discrepancy between the two composition orientations commutes with arbitrary
compatible source and target open restrictions, through the fixed Tate pullback.
Source: composition coherence proof Step 1, diagonal section pasting Step 7,
and the final compatibility paragraph of diagonal DNC chart normalization.
(blueprint: lem-pur-model-orientation-quotient-restriction).

Proof: express the three orientations in their ordinary dualizing presentations
using chartOrdinaryOrientation_spec. The sigma comparison expresses the standing
sigma as the ordinary tensor mate in those presentations. Factor each compatible
open pair into target-open base change and source-open restriction; the latter
is etale but need not be Cartesian over the original target. Apply
chartOrientation_open_baseChange and chartOrientation_etale_restriction to the
three ordinary orientations. Apply the sigma square of diagonalSectionPastingOpen
to the ordinary tensor mate. Naturality of the comparison pullback and monoidal
constraints transports all four squares to the pro-etale site. The two middle
open-dualizing comparisons cancel in the quotient. Canonical Tate pullback
commutes with tensor concatenation, so its remaining target comparison is J,
including the conversion from derived pullback to exact open restriction.
More explicitly, write A = sigma followed by the total orientation and
B = R, with primed analogues. The transported squares give
  F.map A followed by J = S followed by A',
  F.map B.hom followed by J = S followed by B'.hom,
where S is the canonical restriction comparison of the tensor source. Cancel
B'.hom in the second equation to obtain F.map B.inv followed by S = J followed
by B'.inv. Substitute the first equation into F.map(B.inv followed by A)
followed by J, and then this inverse equation; the result is J followed by
B'.inv followed by A', precisely the required quotient square. No affine
equation, rank-one detection, or orientation composition law is used. Empty opens
and rank-zero powers use the same unit constraints. -/
theorem model_orientation_quotient_restriction (P : PurityFiniteSetting.{u})
    {X Y Z X' Y' Z' : Scheme.{u}} (d e : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (u' : X' ⟶ X) (v : Y' ⟶ Y) (w : Z' ⟶ Z)
    [IsOpenImmersion u'] [IsOpenImmersion v] [IsOpenImmersion w]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
    (hf : u' ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w)
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType (w ≫ aZ)] [QuasiCompact (w ≫ aZ)] :
    letI := P.noetherian aZ
    letI := P.noetherian (g ≫ aZ)
    letI := P.noetherian (w ≫ aZ)
    letI := P.noetherian (g' ≫ w ≫ aZ)
    letI := Dnc.compactifiable P f (g ≫ aZ)
    letI := Dnc.compactifiable P g aZ
    letI := Dnc.compactifiable P (f ≫ g) aZ
    letI := Dnc.compactifiable P f' (g' ≫ w ≫ aZ)
    letI := Dnc.compactifiable P g' (w ≫ aZ)
    letI := Dnc.compactifiable P (f' ≫ g') (w ≫ aZ)
    letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    letI := (DiagonalPasting.geometryProperties d e f' g').2.2.2.2
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    let R := P.compatibleTensorIso (P.modelOrientation d f (g ≫ aZ))
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
        (P.modelOrientation e g aZ)) ≪≫ P.modelOrientationMu d e f (g ≫ aZ)
    let R' := P.compatibleTensorIso (P.modelOrientation d f' (g' ≫ w ≫ aZ))
      ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f').leftDerivedFunctor.mapIso
        (P.modelOrientation e g' (w ≫ aZ))) ≪≫
          P.modelOrientationMu d e f' (g' ≫ w ≫ aZ)
    let Q := R.inv ≫ ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
      (P.modelOrientation (d + e) (f ≫ g) aZ).hom
    let Q' := R'.inv ≫ ProEtale.CompositionTensorMate.sigma P.Coefficient f' g' ≫
      (P.modelOrientation (d + e) (f' ≫ g') (w ≫ aZ)).hom
    let J := ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) u').app (P.diagonalTwist X (d + e))).symm ≪≫
        P.modelOrientationTwistPullback u' (f ≫ g ≫ aZ) (d + e)
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) u').mapDerivedCategory.map Q ≫
        J.hom = J.hom ≫ Q' := by
  sorry

end WeilConjectures.PurityFiniteSetting
