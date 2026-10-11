/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma.ProjectiveDomination
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Cancellation
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# The reduction of proper base change to the projective line

Assume that the projection `ℙ¹_S ⟶ S` satisfies the base change property
`AlgebraicGeometry.Etale.HasTorsionBaseChange` for every scheme `S`. Then every proper morphism
satisfies it (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper`).

The proof follows the Stacks Project:

- *change of coefficients*: it suffices to treat the coefficient rings `Λ ⧸ pΛ`, `p` prime,
  which are torsion as additive groups
  (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_forall_prime`), and the hypothesis passes
  to them (`AlgebraicGeometry.Etale.HasTorsionBaseChange.quotient`); for a torsion ring the base
  change property composes and cancels along proper surjections;
- *from `ℙ¹` to `ℙⁿ`*: `(ℙ¹_S)ⁿ ⟶ S` is a composite of projective lines, and the symmetric
  product `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S` is finite and surjective
  (`AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveSpace`);
- *target locality and Chow's lemma*: over an affine open `U` of the target, `f` is dominated by
  a closed subscheme `X̃` of `ℙⁿ_U` through a proper surjection `π : X̃ ⟶ X`; closed immersions are
  finite, so `X̃ ⟶ U` has the base change property, and so does `π`, which factors as the closed
  immersion `X̃ ⟶ ℙⁿ_X` followed by the projection; cancellation along `π` concludes.

## References

- Stacks Project, Lemma 59.91.10, <https://stacks.math.columbia.edu/tag/0A4F>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale ProjectiveSpace

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The tower `(ℙ¹_S)ⁿ ⟶ S` satisfies the base change property if all projective lines do, the
coefficient ring being torsion: it is a composite of projective lines over successive bases. -/
theorem Etale.hasTorsionBaseChange_projectiveLinePowProj (hΛ : IsAddTorsion Λ)
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S)) (n : ℕ)
    (S : Scheme.{u}) : Etale.HasTorsionBaseChange Λ (projectiveLinePowProj n S) := by
  induction n with
  | zero => sorry
  | succ n ih => exact Etale.HasTorsionBaseChange.comp Λ hΛ (h _) ih

/-- **Reduction of projective space to products of lines.** For a torsion coefficient ring `Λ`,
if `ℙ¹_S ⟶ S` satisfies the base change property for every scheme `S`, then so does `ℙⁿ_S ⟶ S`
for every finite index type `n`: the composite `(ℙ¹_S)ᵏ ⟶ ℙⁿ_S ⟶ S` of the finite surjective
symmetric product morphism with the projection is a composite of projective lines, and the base
change property cancels along the finite surjective symmetric product morphism.
(blueprint: `lem-weil-pbc-reduction-projective-space`) -/
theorem Etale.hasTorsionBaseChange_projectiveSpace (hΛ : IsAddTorsion Λ)
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S)) (n : Type u)
    [Finite n] (S : Scheme.{u}) : Etale.HasTorsionBaseChange Λ (ℙ(n; S) ↘ S) :=
  sorry

/-- **Reduction of proper base change to the projective line, torsion coefficients.** For a
coefficient ring `Λ` which is torsion as an additive group, if `ℙ¹_S ⟶ S` satisfies the base
change property for every scheme `S`, then so does every proper morphism.
(blueprint: `prop-weil-pbc-reduction-to-projective-line`) -/
theorem Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper_of_isAddTorsion
    (hΛ : IsAddTorsion Λ)
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : Etale.HasTorsionBaseChange Λ f :=
  sorry

/-- **Reduction of proper base change to the projective line**: if the projection
`ℙ¹_S ⟶ S` satisfies `AlgebraicGeometry.Etale.HasTorsionBaseChange` for every scheme `S`,
then so does every proper morphism of schemes.

The proof is Chow's lemma: a proper `f : X ⟶ Y` is dominated by a projective one,

```
       X̃ ------------> ℙⁿ_Y
       |                |
     π |                | pₙ
       v                v
       X ------ f ----> Y
```

with `π` proper surjective and the horizontal arrow a closed immersion over `Y`; the base
change property for `pₙ` comes from that of `ℙ¹` by the symmetric-product morphism, and
transfers to `f` because it composes and cancels along proper surjections. These manipulations
need a torsion coefficient ring, which is reached by the change of coefficients
`Λ ↝ Λ ⧸ pΛ`.
(blueprint: `sk-thm-reduction`, `prop-weil-pbc-reduction-to-projective-line`) -/
@[stacks 0A4F]
theorem Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_forall_prime Λ f fun p hp ↦
    Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper_of_isAddTorsion _ sorry
      (fun S ↦ (h S).quotient Λ p) f

end AlgebraicGeometry
