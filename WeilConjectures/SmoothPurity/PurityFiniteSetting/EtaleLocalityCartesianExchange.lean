/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointCoherenceSupplement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Etale.EtaleHorizontalDoubleCounit
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientLeftComparisonBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
import WeilConjectures.AlgebraicGeometry.Tensor.TensorMateEtalePrecomp
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Two source-locality maps through a common target-open restriction

Source: orientation-charts proof Step 3, equations (Lj) and (Lv).
Factor source locality by conjugating its compact-support comparison. The horizontal
double-counit formula factors each actual exchange through the same target factor.
Cancel the exact-pullback comparison, evaluate at the unit and apply the fixed
coefficient-unit identifications.
(blueprint: new-lem-pur-etale-locality-cartesian-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Etale.upperStar Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction Functor.mapDerivedCategory
  Functor.rightDerivedFunctor conjugateIsoEquiv

private def rho (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : Etale.EtaleCompactSupportNormalization A)
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [QuasiCompact j]
    [HasCompactification j] :=
  conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction A j)
    (Etale.derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
      inferInstance) (Etale.etaleCanonicalCompactSupportComparison A j N).symm

private def excCongr (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    Etale.rightDerivedUpperShriek A f ≅ Etale.rightDerivedUpperShriek A g :=
  eqToIso (by cases w; rfl)

private theorem congr_conjugate (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [HasCompactification f] [HasCompactification g] (w : f = g) :
    excCongr A w = conjugateIsoEquiv
      (Etale.rightDerivedUpperShriekAdjunction A f)
      (Etale.rightDerivedUpperShriekAdjunction A g)
      (Etale.unboundedEtaleLowerShriekCongr A w).symm := by
  subst g
  apply Iso.ext
  simp only [excCongr, eqToIso_refl, conjugateIsoEquiv_apply_hom,
    Etale.unboundedEtaleLowerShriekCongr, Iso.symm_hom, Iso.refl_inv, Iso.refl_hom,
    conjugateEquiv_id]

end WeilConjectures.PurityFiniteSetting
