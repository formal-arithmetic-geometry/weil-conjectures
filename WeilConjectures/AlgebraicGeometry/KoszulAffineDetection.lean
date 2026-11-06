/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import WeilConjectures.AlgebraicGeometry.PerfectGenerationAffineBase
import WeilConjectures.AlgebraicGeometry.KoszulSupportedAugmentationVanishing
import Mathlib.CategoryTheory.Localization.HomEquiv

/-! # Koszul powers detect supported objects on an affine scheme

Source: Stacks Project, Derived Categories of Schemes, Tag 09IR, proof via
Lemma 36.9.6 and Tag 06Z0 (blueprint: lem-pc-koszul-affine-detection).
-/
