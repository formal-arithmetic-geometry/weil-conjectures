/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleLocalEncodingForward
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleLocalEncodingReverse

/-! # Comparing finite etale models with intrinsic pro-etale local systems

Source: Stacks Project, proetale.tex, Tag 099Y, lemma-compare-locally-constant;
sites-modules.tex, localization of ringed sites, Tag 04IX.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
