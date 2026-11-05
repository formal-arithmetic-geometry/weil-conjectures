/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

/-!
# Admissible condensed coefficients for localizing closures

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
coefficient convention (blueprint: sk-def-localizing-closure).

This supplies the coefficient convention omitted from the recorded localizing-closure
interface. The localizing closure itself is the imported `localizingClosureProEtale`.
The algebraic-closure clause is the finite-subextension-valued ring `padicAlgClRingObj`
(blueprint: sk-def-sfb-qlbar-condensed). The ring of all continuous maps to the algebraic
closure is not an admissible coefficient (removed 2026-10-25).

It also supplies `IsLocalizingSubcategoryOfSize` and `localizingClosureOfSize`, the
imported `IsLocalizingSubcategory` and `localizingClosure` with the index universe of
the direct sums given as a free parameter `w`. At `w = u`, the object universe, they
are the imported definitions. A fixed index universe shared by two categories of
different sizes, as in det-proper-image-localizing-principle, needs this form.
-/

@[expose] public section

set_option autoImplicit false

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
