/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalDncEtaleFactors
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleNormalTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleInverseDeformation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleSourceDualizing

/-! # The deformation and dualizing square of an etale correspondence -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Compatibility of the inverse deformation and dualizing factors with the normal map.
Source: diagonal-dualizing proof Steps 1--2 and its canonicity paragraph;
orientation-charts proof Step 3.

Proof: factor each map of diagonal pairs through Cartesian base change followed by
the etale map on the second factor. Remove the complementary clopen components of
the inverse image of the diagonal. Section-restriction coherence for the normalized
DNC family at one and zero identifies inverse delta through these two operations.
The zero comparison is exactly n, since it is constructed from the same Rees map.
The inverse-deformation square records this step at the actual source invariant.
Paste the smooth exceptional exchange squares and their section equations to obtain
the alpha comparison. Paste the target-open squares to obtain rho. The defining
adjunction mates and their coefficient-unit naturality identify the resulting
ordinary dualizing comparison with B for every normalized N. Cancel the interior
source-section comparisons. The source-to-dualizing square records this second step.
The proof below combines these two independent squares by functoriality and
associativity. It uses no beta, vector integration or coefficient twist orientation.
Empty opens and rank zero obey the same exchange and DNC normalization equations.
(blueprint: lem-pur-diagonal-etale-dnc-dualizing-square). -/
theorem diagonalDncEtaleNaturality_dncDualizing (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    [IsNoetherian X] [IsNoetherian Z] [IsNoetherian Y]
    [HasCompactification f] [HasCompactification g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry f aY d V)
    (K : P.AffineDiagonalGeometry g aY d V)
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
    let B := (P.diagonalEtaleLocality N v g) ≪≫
      (P.diagonalDualizingCongr w) ≪≫ (P.diagonalEtaleLocality N j f).symm
    let n := DiagonalEtaleComparison.normalTransport P d f g aY V H K U j v w
      O jO vO hj hv
    n.hom ≫ (OrientationRefinement.pull P vO).map
        (DiagonalEtaleComparison.normalToDualizing P d g aY V K).hom =
      (OrientationRefinement.pull P jO).map
        (DiagonalEtaleComparison.normalToDualizing P d f aY V H).hom ≫
        (cj.app (P.diagonalOrdinaryDualizing f)).hom ≫
        (T.mapIso (νU.mapIso B)).inv ≫
        (cv.app (P.diagonalOrdinaryDualizing g)).inv := by
  dsimp only
  have hδ := diagonalEtaleInverseDeformation P d f g aY V H K N U j v w
    O jO vO hj hv
  have hs := diagonalEtaleSourceDualizing P d f g aY V H K N U j v w
    O jO vO hj hv
  dsimp only at hδ hs
  simp only [DiagonalEtaleComparison.normalToDualizing,
    DiagonalEtaleComparison.sourceToDualizing, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc] at hs ⊢
  rw [reassoc_of% hδ, hs]

end WeilConjectures.PurityFiniteSetting
