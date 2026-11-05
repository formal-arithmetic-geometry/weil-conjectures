/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceHeartOrigin
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceModelTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology

/-! # Etale derived origin on a finite-coefficient slice

Source: Stacks Project, proetale.tex, Tag 09AL
(blueprint: lem-weil-pbc-finite-coefficient-etale-slice-origin).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

-- Keep the original signature, including its unused interval and arrow binders.

end AlgebraicGeometry.Scheme
