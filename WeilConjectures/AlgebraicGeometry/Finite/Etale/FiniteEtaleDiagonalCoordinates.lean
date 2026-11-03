/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
public import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.Finite.Smooth.FiniteSmoothGammaConstructions
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteEtaleSpecializationCoordinates

/-! # Diagonal exceptional base change in etale unit coordinates

Source: latest blueprint sec-smooth-purity/sk-prop-sp-orientation, first factor.
(blueprint: lem-pur-finite-etale-diagonal-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The diagonal factor respects the coefficient-unit coordinates supplied by the
same graph-normalized etale sum comparison on the map and its first projection.
Source: sk-prop-sp-orientation.proof.md, first paragraph and first displayed arrow;
lem-pur-finite-smooth-gamma-normalization, proof Steps 1 and 3.
(blueprint: lem-pur-finite-etale-diagonal-coordinates).

Proof: graph extension specifies the sheaf comparison uniquely, since its composite
with the monomorphism from extension by zero to direct image is prescribed. Its
degreewise homotopy normalization then specifies the derived comparison uniquely.
Thus the supplied comparison agrees with the exchange-compatible comparison of
etaleSupportMapCompatibility. Apply that exchange identity to the square defining
p_1, the base change of f along f. Transpose under the two exceptional adjunctions.
The sum-extension exchange is the mate of the inverse-image compositor: its
unit--exchange--counit formula cancels by the two triangle identities. Consequently
the exceptional mate in adjoint coordinates is precisely this compositor. Evaluate
at the coefficient unit, using naturality of the inverse-image unit comparisons,
and pull back by the diagonal. The equality Delta followed by p_2 = id cancels the
section compositor in finiteSmoothDiagonalFactor. The surviving unit comparison
is exactly finiteSmoothOmegaCoordinates. This calculation uses neither deformation
nor integration, and applies also to empty schemes and the zero coefficient ring. -/
theorem finiteEtaleDiagonalCoordinates
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f] [Etale f]
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C) :
    finiteSmoothDiagonalFactor A f ≫
        (finiteSmoothSectionCoordinates A C (pullback.fst f f) (pullback.diagonal f)).hom =
      (finiteSmoothOmegaCoordinates A C f).hom := by
  let J := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)
  have hb := FiniteSmoothPurity.omega_coordinates_baseChange A
    (IsPullback.of_hasPullback f f).flip C hC
  dsimp only [finiteSmoothDiagonalFactor, finiteSmoothSectionCoordinates,
    Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  rw [hb]
  simp only [Functor.map_comp, Category.assoc]
  erw [← FiniteSmoothPurity.derived_pullback_section_unit A
    (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)]
  have hn := J.hom.naturality (finiteSmoothOmegaCoordinates A C f).hom
  simp only [Functor.comp_map] at hn
  erw [hn, Iso.inv_hom_id_app_assoc]
  rfl

end AlgebraicGeometry.Etale
