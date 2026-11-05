/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart1Supplement3

/-! # Retaining a closed subset in the principal w-localization

Source: blueprint, proper base change, Retaining a closed subset, order 1224
(blueprint: def-weil-pbc-retained-localization).

Selectors are constructed at the two-part partition into a constructible set and its
complement, omitting empty parts. Their localizations form a reverse-inclusion diagram.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization.Retained

variable {R : Type u} [CommRing R]

attribute [instance] neighborhood_isFiltered

end PrincipalWLocalization.Retained
