/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence

/-!
# Retired duplicate (2026-10-17)

The source library proves blueprint node
`lem-weil-pbc-grothendieck-spectral-sequence`
sorry-free as
`AlgebraicGeometry.Etale.exists_grothendieckSpectralSequence_lowerStar`
in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence`
This module re-exports it. Its sorried declaration
`AlgebraicGeometry.Etale.exists_module_grothendieck_spectralSequence`
is gone (no module used it).
-/
