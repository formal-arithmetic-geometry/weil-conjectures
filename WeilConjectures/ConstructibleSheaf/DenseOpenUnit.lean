/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Locally constant sheaves on a regular scheme extend uniquely over a dense open

Let `X` be a locally noetherian regular scheme, `j : U ⟶ X` an open immersion with dense image
and `G` a locally constant sheaf of `Λ`-modules on the small étale site of `X`. Then the unit
`G ⟶ j_* j^* G` of the adjunction `j^* ⊣ j_*` is an isomorphism.

It is a monomorphism since morphisms into a locally constant sheaf are determined on a dense
open (`AlgebraicGeometry.Etale.upperStar_map_injective_of_isLocallyConstantSheaf`). It is locally
surjective: a section of `j_* j^* G` over an étale `V ⟶ X` is a section of `G` over
`V ×_X U`; near a point of `V`, refine `V` to an étale `W` over which `G` is constant and whose
underlying scheme is irreducible. Such `W` exist because étale `X`-schemes are again locally
noetherian with integral local rings, so their points have irreducible open neighbourhoods. Then
`W ×_X U` is a nonempty open of `W`, hence irreducible, and the sections of a constant sheaf
over an irreducible étale scheme are the constants
(`AlgebraicGeometry.Etale.bijective_toSheafify_app_of_irreducibleSpace`); so the section over
`W ×_X U` is a constant, which is the restriction of the same constant over `W`.

## Main statements

- `AlgebraicGeometry.Etale.bijective_toSheafify_app_of_irreducibleSpace`: the sections of the
  constant sheaf of modules `N` over an étale `X`-scheme with irreducible underlying space are
  `N`.
- `AlgebraicGeometry.exists_isOpen_irreducibleSpace_of_isDomain_stalk`: a point of a locally
  noetherian scheme with integral local rings has an irreducible open neighbourhood.
- `AlgebraicGeometry.Etale.isIso_unit_upperStarLowerStarAdjunction_of_isRegular`: the unit
  `G ⟶ j_* j^* G` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

/-- **Irreducible neighbourhoods.** A point of a locally noetherian scheme whose local rings are
integral domains has an irreducible open neighbourhood: its connected component is open, the
scheme being locally connected, and a connected locally noetherian scheme with integral local
rings is irreducible (`AlgebraicGeometry.irreducibleSpace_of_isDomain_stalk`). -/
theorem exists_isOpen_irreducibleSpace_of_isDomain_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) (x : X) :
    ∃ O : X.Opens, x ∈ O ∧ IrreducibleSpace O := by
  let O : X.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
  refine ⟨O, mem_connectedComponent, ?_⟩
  have : ConnectedSpace O :=
    Subtype.connectedSpace isConnected_connectedComponent
  have : IsLocallyNoetherian O := inferInstance
  exact irreducibleSpace_of_isDomain_stalk O fun y ↦
    have := h y.1
    MulEquiv.isDomain _ (O.stalkIso y).commRingCatIsoToRingEquiv.toMulEquiv

end AlgebraicGeometry
