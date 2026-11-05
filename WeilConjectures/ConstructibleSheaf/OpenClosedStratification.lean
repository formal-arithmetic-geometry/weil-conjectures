/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The stratification attached to an open subset of a closed subscheme

Let `X` be a noetherian scheme, `ι : Z ⟶ X` a closed immersion and `V ⊆ Z` an open subset. The
three locally closed subsets `X ∖ Z`, `V` and `Z ∖ V` form a stratification of `X`
(`AlgebraicGeometry.Scheme.Stratification.ofClosedImmersionOpens`), with the open subscheme
`X ∖ Z`, the open subscheme `V` of `Z` and the reduced closed subscheme on `Z ∖ V` as schemes.
On a noetherian scheme every locally closed subset is constructible
(`IsLocallyClosed.isConstructible_of_noetherianSpace`).

-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Scheme

variable {X Z : Scheme.{u}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : Z.Opens)

/-- The open complement `X ∖ Z` of a closed immersion `ι : Z ⟶ X`. -/
noncomputable def openComplementOfIsClosedImmersion : X.Opens :=
  ⟨(Set.range ι.base)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩

end AlgebraicGeometry.Scheme
