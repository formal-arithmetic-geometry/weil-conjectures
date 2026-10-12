/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction

/-!
# Local constancy under open restriction

Source: finite pushforward constructibility blueprint, step 2; Stacks Project, Tag 093R.
(blueprint: lem-weil-pbc-etale-locally-constant-open-pullback).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Restricting a locally constant set-valued etale sheaf to an open subscheme preserves
local constancy. No finiteness or Noetherian hypothesis is needed.

Source: blueprint `lem-weil-pbc-finite-pushforward-constructible-noetherian`, step 2;
Stacks Project, Modules on Sites, Lemma 093R; Etale Cohomology, Tags 03S2 and 00XZ.
(blueprint: lem-weil-pbc-etale-locally-constant-open-pullback).

Proof: Choose an etale cover trivializing F on its localized sites. Base change that
cover along the open immersion U into X. The resulting family is an etale cover of U.
For each original cover member V, the new member is the open subscheme V times_X U.
Identify etale sheaves on V with sheaves on the site of X localized at V. Restriction
to V times_X U is localization once more. Under this identification the restriction
of F is constant: the over-pullback functor carries the constant sheaf to the constant
sheaf, by the adjunction for constant sheaves (equivalently, sheafify the restricted
constant presheaf; the localization functor preserves covering families).
The etale inverse-image restriction comparison identifies the restriction of the
inverse image on U with that same twice-localized sheaf; its unit compatibility makes
the two restrictions agree. Isomorphic sheaves have the same constant-sheaf property.
Thus the base-changed cover is a trivializing cover of the inverse image on U. -/
theorem isLocallyConstantEtaleSheafOfSets_open_pullback
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (U : X.Opens) (hF : IsLocallyConstantEtaleSheafOfSets F) :
    IsLocallyConstantEtaleSheafOfSets ((etaleSetPullback U.ι).obj F) := by sorry

end AlgebraicGeometry.Scheme
