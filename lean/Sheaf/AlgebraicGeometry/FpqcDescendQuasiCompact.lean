import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Quasi-compactness descends along flat surjective quasi-compact morphisms

Source: literature/stacks-project/descent.tex, Descent, Lemma Tag 02KQ
(lemma-descending-property-quasi-compact) (blueprint: lem-weil-pbc-fpqc-descend-quasi-compact).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Quasi-compactness descends along a flat, surjective, quasi-compact morphism.

The proof follows Descent, Lemma Tag 02KQ
(blueprint: lem-weil-pbc-fpqc-descend-quasi-compact).  For an affine open `U` of `S`,
put `V := g ⁻¹' U`; quasi-compactness of `g` makes `V` quasi-compact.  Put
`X' := X ×ₛ S'` and `W := f' ⁻¹' V`, where `f'` is the second projection;
quasi-compactness of `f'` and the quasi-compact-open preimage lemma make `W`
quasi-compact.  The projection `X' ⟶ X` is surjective by base change of `g`,
and its image of `W` is exactly `f ⁻¹' U`.  This image is quasi-compact by
continuity of the projection and the continuous-image lemma.  Since this holds
for every affine `U`, the definition of `QuasiCompact f` concludes.  The
`Flat g` hypothesis is retained as part of the fpqc covering hypothesis, even
though this final topological argument uses only surjectivity and
quasi-compactness of `g`.
-/
theorem quasiCompact_of_fpqc_baseChange {S S' X : Scheme.{u}} (g : S' ⟶ S)
    [Flat g] [Surjective g] [QuasiCompact g] (f : X ⟶ S)
    [QuasiCompact (pullback.snd f g)] : QuasiCompact f := by
  sorry

end AlgebraicGeometry
