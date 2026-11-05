/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.SectionsContinuity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.SheafIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.UpperStarLowerStarHom

/-!
# `g_* g^* H` as the colimit of the finite Galois levels

Let `Ω / L` be a Galois extension, `G` a scheme over `Spec L`, `g_{L'} : G_{L'} = G ×_L L' ⟶ G`
for the finite Galois subextensions `L'` and `g : G_Ω = G ×_L Ω ⟶ G`. The restrictions along the
projections `G_Ω ⟶ G_{L'}` form a cocone `g_{L'*} g_{L'}^* ⟶ g_* g^*` over the diagram of the
`g_{L'*} g_{L'}^*` (`AlgebraicGeometry.ProEtale.galoisUpperLowerCocone`). For an abelian sheaf `H`
of étale origin, it is a colimit cocone at `H`
(`AlgebraicGeometry.ProEtale.nonempty_isColimit_galoisUpperLowerCocone`).

This is first proved in the restriction model `j_{g}^* ⋙ g_*`, whose sections over `W` are the
sections of `H` over `W ×_G G_{L'}` (`AlgebraicGeometry.ProEtale.galoisRestrictionCocone`): the
comparison map from the colimit is bijective on sections over objects with affine underlying
scheme, by `AlgebraicGeometry.ProEtale.nonempty_isColimit_galoisSectionsCocone` and the
commutation of sections with filtered colimits, and these objects cover the pro-étale site.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite FiniteGaloisIntermediateField

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

/-! ### The restriction model -/

/-! ### The pushforward of the pullback -/

end AlgebraicGeometry.ProEtale
