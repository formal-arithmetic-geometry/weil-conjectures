/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Endomorphism

/-! # The fixed ideal of a subgroup of scheme automorphisms

Source: ILO, Travaux de Gabber, VI 4.1--4.2 and 4.7--4.8
(blueprint: def-per-scheme-action-fixed-ideal).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The ideal of the common fixed subscheme is the sum of the ideals of the equalizers
of each subgroup element with the identity. For a separated scheme these equalizers
are closed immersions; the sum therefore defines their scheme-theoretic intersection,
including its nonreduced structure. No invariant open or log structure is chosen.
Source: ILO VI 4.1--4.2 and 4.7 (blueprint: def-per-scheme-action-fixed-ideal). -/
noncomputable def schemeActionFixedIdeal {G : Type v} [Group G] {X : Scheme.{u}}
    [X.IsSeparated] (a : G →* Aut X) (K : Subgroup G) : X.IdealSheafData :=
  ⨆ g : K, (equalizer.ι (a g).hom (𝟙 X)).ker

end AlgebraicGeometry
