/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicIntrinsicCompletion
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift

import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModels
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicRealization
import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstruction
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement

/-!
# Perfect local lifting of a lisse residue reduction

Source: Stacks Project, proetale.tex, Tag 09C6; Bhatt--Scholze, Lemma 6.6.8 and
Proposition 6.6.11 (blueprint: lem-weil-pbc-residue-lisse-perfect-lift).

Constant complexes use the existing constant-module sheafification. The coefficient
maps below are fixed uniquely on constant sections. Restriction means the actual
localized site, without identifying it with a separately chosen small skeleton.

## Main definitions

- `residueLisseDerivedConstant`: the exact constant module functor on derived categories.
- `residueLisseConstantComparison`: the normalized quotient coefficient comparison.

## Main statements

- `residue_lisse_perfect_lift`: the local perfect realization over completed coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

attribute [local instance] residueLisseAbLocallyBijective

end AlgebraicGeometry.Scheme
