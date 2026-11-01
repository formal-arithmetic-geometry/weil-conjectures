/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleAlphaSquare
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalEtaleRhoUnitSquare

/-! # The source invariant and dualizing locality

Source: diagonal-dualizing proof Steps 1--2 and orientation-charts proof Step 3.
(blueprint: lem-pur-diagonal-etale-source-dualizing-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The diagonal source invariant maps naturally to the ordinary dualizing object.
This compares only alpha, target-open rho and the coefficient-unit comparison;
there is no deformation map, normal invariant, beta or vector integration.
Source: diagonal-dualizing proof Steps 1--2 and final canonicity paragraph;
orientation-charts proof Step 3, first paragraph.

Proof: for each of jO and vO, factor the self-product map through the base change
of the first projection. Source-etale/base-change interchange and mate pasting
compare the two factorizations of the self-product counit square. Pull the equality
to the diagonal. Its second-projection composite is the identity, so pullback
composition cancels the interior section constraints. Inverting the self-product
base-change mates gives the alpha square with the actual source map constructed
from normalized locality and smooth section base change. Paste with the Cartesian
target-open square to compare rho. Apply naturality of these same mates to the
isomorphism from the monoidal unit to the degree-zero coefficient unit. This gives
the unitChange square, with the ordinary source-etale comparison diagonalEtaleLocality
for N. Inverse-image composition and site-comparison naturality give restrictionAlong
for hj and hv. Compose the resulting two one-sided squares through the common
source diagonal. Their common alpha and target restriction cancel; equality of
v followed by g and j followed by f supplies diagonalDualizingCongr w. The remaining
outer comparison is precisely B inverse. Normalization fixes the same maps for every
N. The argument uses no purity orientation and includes rank zero and empty opens.
(blueprint: lem-pur-diagonal-etale-source-dualizing-square). -/
theorem diagonalEtaleSourceDualizing (P : PurityFiniteSetting.{u})
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
    let s := DiagonalEtaleComparison.sourceTransport P d f g aY V H K N U j v w
      O jO vO hj hv
    s.hom ≫ (OrientationRefinement.pull P vO).map
        (DiagonalEtaleComparison.sourceToDualizing P d g aY V K).hom =
      (OrientationRefinement.pull P jO).map
        (DiagonalEtaleComparison.sourceToDualizing P d f aY V H).hom ≫
        (cj.app (P.diagonalOrdinaryDualizing f)).hom ≫
        (T.mapIso (νU.mapIso B)).inv ≫
        (cv.app (P.diagonalOrdinaryDualizing g)).inv := by
  dsimp only
  have ha := diagonalEtaleAlphaSquare P d f g aY V H K N U j v w O jO vO hj hv
  have hr := diagonalEtaleRhoUnitSquare P d f g aY V H K N U j v w O jO vO hj hv
  dsimp only at ha hr
  simp only [DiagonalEtaleComparison.sourceToDualizing, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at hr ⊢
  rw [reassoc_of% ha, hr]

end WeilConjectures.PurityFiniteSetting
