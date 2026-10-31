/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncEtaleNaturalityTwist

/-! # Etale naturality of the local DNC orientation

Source: blueprint latest, diagonal-dualizing-object proof, Steps 1--3 and canonicity.
(blueprint: lem-pur-diagonal-dnc-etale-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The DNC comparison commutes with an etale correspondence over the target.
This assertion involves no affine trace or projective-line datum.
Source: diagonal-dualizing-object proof, Steps 1--3 and canonicity paragraph
(blueprint: lem-pur-diagonal-dnc-etale-naturality).

Proof: restrict the correspondence to O. On the self-products use first Cartesian
base change of the diagonal pair, and then the etale map on the other factor.
The inverse image of the diagonal is a disjoint union of open-and-closed components;
retain the component containing the section. Section restriction and its counit
are unchanged by this removal. The induced conormal map fixes da, represented by
a tensor 1 minus 1 tensor a. Thus the normal map is the same coefficientwise Rees
map as in the deformation family. The family equation and uniqueness of normalized
DNC invariance give the delta square. Choose a vector model on each side, use a
common local frame, and apply BetaNormalized. Vector integration base change and
linear trace invariance give the beta square; the frame changes introduce no scalar.
For alpha, paste the two self-product squares and the section identities. The mate
pasting law gives the source-etale locality square. For rho, paste with the target
open square. Its mate is the prescribed open restriction. Multiply these four
squares, cancel the adjacent comparison inverse pairs, and insert the two ordinary
Tate pullbacks. Site comparison and composition produce restrictionAlong on both
sides. The sum-extension counit characterization fixes the locality maps for every
normalized N. Equality is local on the shifted rank-one Tate source: after shifting
into degree zero, sheaf-Hom gluing detects equality. This also covers empty O and
d=0, when the frame is empty and all Tate products are units. -/
theorem diagonalDncEtaleNaturality (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    [IsNoetherian X] [IsNoetherian Z] [IsNoetherian Y]
    [HasCompactification f] [HasCompactification g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (C : OrientationRefinement.Chart P f aY d V)
    (E : OrientationRefinement.Chart P g aY d V)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (v : U ⟶ Z) [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : v ≫ g = j ≫ f)
    [HasCompactification (j ≫ f)] [HasCompactification (v ≫ g)]
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    (vO : O.toScheme ⟶ (g ⁻¹ᵁ V.1).toScheme)
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j)
    (hv : vO ≫ (g ⁻¹ᵁ V.1).ι = O.ι ≫ v) :
    let νU := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
    let T := OrientationRefinement.pull P O.ι
    let cj := OrientationCounit.restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj
    let cv := OrientationCounit.restrictionAlong P v (g ⁻¹ᵁ V.1) O vO hv
    let a :=
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t v (P.diagonalExponent_isUnit (g ≫ aY)) d).inv
    let b := (P.diagonalEtaleLocality N v g).hom ≫
      (P.diagonalDualizingCongr w).hom ≫ (P.diagonalEtaleLocality N j f).inv
    T.map (νU.map a) ≫
        (cv.app (P.diagonalTwistEtale Z d)).inv ≫
        (OrientationRefinement.pull P vO).map
          (OrientationCounit.localInverse P d g aY V E).hom ≫
        (cv.app (P.diagonalOrdinaryDualizing g)).hom ≫ T.map (νU.map b) =
      (cj.app (P.diagonalTwistEtale X d)).inv ≫
        (OrientationRefinement.pull P jO).map
          (OrientationCounit.localInverse P d f aY V C).hom ≫
        (cj.app (P.diagonalOrdinaryDualizing f)).hom := by
  let νU := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
  let T := OrientationRefinement.pull P O.ι
  let cj := OrientationCounit.restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj
  let cv := OrientationCounit.restrictionAlong P v (g ⁻¹ᵁ V.1) O vO hv
  let a :=
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom ≫
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t v (P.diagonalExponent_isUnit (g ≫ aY)) d).inv
  let B := (P.diagonalEtaleLocality N v g) ≪≫
    (P.diagonalDualizingCongr w) ≪≫ (P.diagonalEtaleLocality N j f).symm
  let b := B.hom
  have h := diagonalDncEtaleNaturality_twist P d f g aY V C E t N U j v w O jO vO hj hv
  dsimp only at h ⊢
  have hh := congrArg (fun z ↦
    z ≫ (cv.app (P.diagonalOrdinaryDualizing g)).hom ≫
      T.map (νU.map b)) h
  have hcancel :
      T.map (νU.map ((P.diagonalEtaleLocality N v g) ≪≫
          (P.diagonalDualizingCongr w) ≪≫ (P.diagonalEtaleLocality N j f).symm).inv) ≫
        T.map (νU.map ((P.diagonalEtaleLocality N v g).hom ≫
          (P.diagonalDualizingCongr w).hom ≫ (P.diagonalEtaleLocality N j f).inv)) = 𝟙 _ := by
    simp only [← Functor.map_comp, Iso.trans_inv, Iso.symm_inv, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id, νU.map_id, T.map_id]
  simpa [cv, T, νU, B, b, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Category.comp_id,
    Category.id_comp, Iso.trans_hom, Iso.symm_hom, hcancel] using hh

end WeilConjectures.PurityFiniteSetting
