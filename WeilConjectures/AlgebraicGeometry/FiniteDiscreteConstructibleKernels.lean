/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientEncodingData
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodedPresentation
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

set_option linter.privateModule false

/-! # Kernels of constructible internal modules with finite discrete coefficients

Source: Bhatt--Scholze, Section 5.1 and Lemma 5.4.1, and the noetherian constructible
Serre theorem. Finite presentations are compared before passing to derived categories.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Maps from the internal regular module are determined by the image of one.

-- The specified equivalence G need not fix the regular module definitionally.
-- Identify the two representing objects using hG and fully faithful coyoneda.

-- A finite presentation over B sheafifies to a finite internal presentation.

end AlgebraicGeometry.ProEtale.CondensedRing
