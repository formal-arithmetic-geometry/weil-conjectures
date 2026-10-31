/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
public import WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceEndpoint

/-! # Coefficient-unit naturality of normalized etale locality

Source: diagonal-dualizing proof Step 2; orientation-charts proof Step 3.
(blueprint: lem-pur-diagonal-etale-locality-unit-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  Functor.mapDerivedCategory Functor.rightDerivedFunctor conjugateIsoEquiv

private theorem locality_unit (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {U X Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (f : X ⟶ Y) [HasCompactification f] [HasCompactification (j ≫ f)] :
    (Etale.ordinaryFinitePullback P.Coefficient j).map
        (OrientationCounit.unitChange P f).hom ≫ (P.diagonalEtaleLocality N j f).hom =
      (Etale.sectionStructuralLocalityIso P.Coefficient j f (j ≫ f) rfl).hom ≫
        (OrientationCounit.unitChange P (j ≫ f)).hom := by
  let ell := Functor.isoWhiskerLeft
      (Etale.rightDerivedUpperShriek P.Coefficient f)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) j) ≪≫
    Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N j f
  rw [DiagonalEtaleComparison.locality_tensorMate P.Coefficient N j f]
  exact ell.hom.naturality
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).inv

/-- Normalized etale exceptional locality respects the fixed coefficient-unit change.
Source: diagonal-dualizing proof Step 2; orientation-charts proof Step 3.

Proof: the pullback comparison followed by the tensor-mate locality is a natural
isomorphism on the entire unbounded derived category of the target. Apply its
naturality to the inverse of the monoidal-unit/degree-zero coefficient isomorphism.
On the monoidal unit this natural isomorphism is the counit-normalized structural
locality. On the coefficient object it is diagonalEtaleLocality. Substitution in
the equality j ≫ f = h supplies the indicated diagonalDualizingCongr.
This argument also applies to empty schemes.
(blueprint: lem-pur-diagonal-etale-locality-unit-change). -/
theorem diagonalEtaleLocality_unitChange (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {U X Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (f : X ⟶ Y) [HasCompactification f] [HasCompactification (j ≫ f)]
    (h : U ⟶ Y) [HasCompactification h] (he : j ≫ f = h) :
    (Etale.ordinaryFinitePullback P.Coefficient j).mapIso
        (OrientationCounit.unitChange P f) ≪≫
      P.diagonalEtaleLocality N j f ≪≫ P.diagonalDualizingCongr he =
    Etale.sectionStructuralLocalityIso P.Coefficient j f h he ≪≫
      OrientationCounit.unitChange P h := by
  subst h
  apply Iso.ext
  simpa only [diagonalDualizingCongr, eqToIso_refl, Iso.trans_hom,
    Iso.refl_hom, Functor.mapIso_hom, Category.comp_id] using locality_unit P N j f

end WeilConjectures.PurityFiniteSetting
