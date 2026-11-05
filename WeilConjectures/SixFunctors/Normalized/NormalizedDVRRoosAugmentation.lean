/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRFlatCokernel
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.LinearScalarCone.LinearScalarCone
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRStrictCoefficientAdjoint

/-! # Coefficient augmentation of the canonical strict DVR Roos object

Source: Stacks Tags 06YS, 06YY, 03EK and 05RT; blueprint DVR effectivity,
proof paragraphs 3--4. (blueprint: lem-coef-normalized-dvr-roos-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/- STATEMENT-DISPUTED (pre-repair): successor-compatible D(R) level isomorphisms
allow Bockstein twists. The finite coefficient compatibility below repairs this;
see coord/changes/W3-DVR-strict-coefficient-augmentation.md for the counterexample. -/

end WeilConjectures
