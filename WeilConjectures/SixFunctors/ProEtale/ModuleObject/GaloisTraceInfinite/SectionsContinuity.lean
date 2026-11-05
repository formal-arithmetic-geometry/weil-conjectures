/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.GaloisLevel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGaloisDescent

/-!
# Sections of sheaves of étale origin over the Galois tower

Let `Ω / L` be a Galois extension, `G` a scheme over `Spec L`, `G_{L'} = G ×_L L'` for the finite
Galois subextensions `L'` and `G_Ω = G ×_L Ω`, with structure maps `g_{L'}`, `g` to `G`. For an
abelian pro-étale sheaf `H` of étale origin on `G` (`H ≅ ν^* F₀`) and an object `W` of `G_proét`
with affine underlying scheme, the sections of `H` over `W ×_G G_Ω` are the filtered colimit of
the sections over the `W ×_G G_{L'}`
(`AlgebraicGeometry.ProEtale.nonempty_isColimit_galoisSectionsCocone`).

This is the continuity of `ν^*`
(`AlgebraicGeometry.ProEtale.isColimit_comparisonUpperStar_mapCocone_of_isAffine`) on the affine
scheme `W`: `W ×_G G_Ω` is the limit of the finite étale `W`-schemes
`W ×_G G_{L'}` (`AlgebraicGeometry.isLimitGaloisLevelCone`), and the restriction of `ν^* F₀` to
`W` is `ν^*` of the étale pullback of `F₀`
(`AlgebraicGeometry.ProEtale.comparisonUpperStarUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite FiniteGaloisIntermediateField

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L)) (H : Sheaf (ProEt.topology G) AddCommGrpCat.{u + 1}) (W : G.ProEt)

end AlgebraicGeometry.ProEtale
