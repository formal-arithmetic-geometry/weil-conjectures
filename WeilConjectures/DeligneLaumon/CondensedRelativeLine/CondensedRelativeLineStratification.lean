/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseRestriction
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.Topology.Homeomorph.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
import WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget
import WeilConjectures.AlgebraicGeometry.UniversallyHomeomorphIntegral
import Mathlib.AlgebraicGeometry.Cover.Open
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.NoetherNormalization
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Relative-line stratification with condensed coefficients

Source: latest blueprint, sec-deligne-laumon-general/sk-prop-wgen-relative-line,
thm-zl-relative-line-stratification.md and its proof, paragraphs 1--4
(blueprint: thm-zl-relative-line-stratification).

All strata are schemes over the original finite field through their immersions.
The geometric line is the geometric fibre of the model line, canonically the line
on the geometric base. The final equality specifies the restricted Weil structure.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedRelativeLine

/-- The relative affine line, with its composite structure map to the finite field.
Source: latest blueprint, thm-zl-relative-line-stratification.md, opening sentence
(blueprint: thm-zl-relative-line-stratification). -/
abbrev lineModel (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀))) :
    Over (Spec (.of D.k₀)) :=
  Over.mk ((AffineSpace (ULift (Fin 1)) Y₀.left ↘ Y₀.left) ≫ Y₀.hom)

/-- Base change of the actual model immersion, with its two canonical projections.
Source: latest blueprint, thm-zl-relative-line-stratification.md, model-defined strata
(blueprint: thm-zl-relative-line-stratification). -/
abbrev geometricInclusion (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {S₀ : Scheme.{u}} (j₀ : S₀ ⟶ X₀.left) :
    pullback (j₀ ≫ X₀.hom) (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ⟶
      (D.geometricFiber X₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
    (Over.homMk j₀ rfl : Over.mk (j₀ ≫ X₀.hom) ⟶ X₀)).left

end WeilConjectures.CondensedRelativeLine
