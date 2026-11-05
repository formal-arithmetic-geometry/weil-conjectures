/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.SixFunctors.Open.OpenQuotientKoszulCompleteness

/-! # Normalized DVR coefficient comparison without open-completeness data

Source: Bhatt--Scholze, Definition 6.5.1 and Lemma 6.5.8(1).
(blueprint: lem-weil-pbc-integral-residue-coefficient-model).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale WeilConjectures
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
