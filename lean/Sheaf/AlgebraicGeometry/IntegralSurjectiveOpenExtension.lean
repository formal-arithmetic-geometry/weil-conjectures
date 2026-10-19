/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.Morphisms.OpenRelativeNormalizationGluing
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Extension of a surjective integral morphism from an open

Source: Stacks Project, More on Morphisms, Tag 0CNX, lemma-extend-integral-surjective-morphisms
(blueprint: lem-trf-integral-surjective-open-extension).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-trf-integral-surjective-open-extension)
Let `j : U ⟶ S` be an open immersion and `g : V ⟶ U` a surjective integral
morphism.  There are a scheme `Vbar`, a surjective integral morphism
`q : Vbar ⟶ S`, and an isomorphism from `Vbar ×_S U` to `V` over `U`.
The proof follows Stacks Project, More on Morphisms, Tag 0CNX:
first glue affine integral-closure charts over the arbitrary open using
localization-compatible principal affine refinements; then adjoin the
reduced closed complement of the open and take the finite coproduct.  The
localization compatibility gives the cocycle for gluing, integrality is
preserved by the coproduct construction, and surjectivity follows from the
surjectivity over the open together with the closed complement.  Finally,
base change of the coproduct along `j` removes the complement and recovers
`V` over `U`.  The argument uses
`lem-trf-open-relative-normalization-gluing`,
`lem-weil-pbc-integral-closure-commutes-localization`,
`lem-weil-pbc-reduced-induced-closed-subscheme`, and
`lem-weil-pbc-scheme-coproduct-family`.
-/
theorem exists_surjective_integral_extension
    {S U V : Scheme.{u}} (j : U ⟶ S) (g : V ⟶ U)
    [IsOpenImmersion j] [IsIntegralHom g] [Surjective g] :
    ∃ (Vbar : Scheme.{u}) (q : Vbar ⟶ S),
      IsIntegralHom q ∧ Surjective q ∧
        ∃ (e : Limits.pullback q j ≅ V), e.hom ≫ g = Limits.pullback.snd q j := by
  sorry

end AlgebraicGeometry
