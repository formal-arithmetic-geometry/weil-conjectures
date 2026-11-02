/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Conventions
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedConstantExtensionFrobenius
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.DeligneLaumon.CondensedWeil.ConstantExtensionPunctualWeights
public import WeilConjectures.PoincareDuality.Poincare
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SmoothPurity.OrientedPerfectDuality
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeightsEmbedding
public import WeilConjectures.Compactification.Affine
public import WeilConjectures.WeilSheaf.LowerShriek

/-!
# Deligne--Laumon affine-line degree-one upper bound

Source: latest blueprint, sec-deligne-laumon-a1/sk-thm-dl-a1-upper/_section.md
(blueprint: sk-thm-dl-a1-upper).

This module states the condensed-coefficient degree-one estimate.  Its postponed
proof has five steps: (1) filter a lisse Weil sheaf by irreducible factors and
inherit purity and unramifiedness; (2) identify geometrically constant factors
with constant rank-one twists and use their degree-one vanishing; (3) apply the
Fourier or middle-extension bound to each nonconstant factor; (4) use the exact
ordinary-direct-image sequence and compact-support triangle, with the degree-zero
endpoint injection; and (5) induct on the filtration, using the subquotient and
extension weight bounds to obtain the upper bound `w + 1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.DeligneLaumon.AffineLine

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
variable {U₀ : Over (Spec (.of D.k₀))}
variable [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]

/-- The affine-line model over the finite field.

Source: rem-dl-a1-conventions, affine-line model paragraph
(blueprint: rem-dl-a1-conventions).
-/
abbrev affineLineModel : Over (Spec (.of D.k₀)) :=
  Over.mk (baseLine D ↘ Spec (.of D.k₀))

/-- The affine-line model is locally of finite type over the finite field.

Source: rem-dl-a1-conventions, affine-line model paragraph
(blueprint: rem-dl-a1-conventions).
-/
instance affineLineModel_lft : LocallyOfFiniteType (affineLineModel D).hom := by
  dsimp [affineLineModel, baseLine]
  infer_instance

/-- The affine-line model is quasi-compact over the finite field.

Source: rem-dl-a1-conventions, affine-line model paragraph
(blueprint: rem-dl-a1-conventions).
-/
instance affineLineModel_qc : QuasiCompact (affineLineModel D).hom := by
  dsimp [affineLineModel, baseLine]
  infer_instance

/-- The affine-line model is separated over the finite field.

Source: rem-dl-a1-conventions, affine-line model paragraph
(blueprint: rem-dl-a1-conventions).
-/
instance affineLineModel_sep : IsSeparated (affineLineModel D).hom := by
  dsimp [affineLineModel, baseLine]
  infer_instance

/-- A chosen Nagata compactification of the affine-line structure map.

Source: the affine compactification construction, `hasCompactification_of_over`
(blueprint: sk-thm-dl-a1-upper).
-/
noncomputable def affineLineCompactification : Compactification (affineLineModel D).hom :=
  HasCompactification.compactification (affineLineModel D).hom
    (hf := hasCompactification_of_over (k₀ := D.k₀) (affineLineModel D).hom)

end WeilConjectures.DeligneLaumon.AffineLine
