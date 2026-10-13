/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Subsheaves of constructible sheaves on noetherian schemes

On a scheme whose underlying space is noetherian, every subsheaf of a constructible étale sheaf
of modules over a noetherian ring is constructible.

## Main statements

- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_mono`: subsheaves of constructible sheaves
  are constructible.

## References

- Stacks Project, Lemma 59.74.1 (03RZ) and Lemma 59.74.3,
  <https://stacks.math.columbia.edu/tag/09BH>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- **Subsheaves of a constructible sheaf on a noetherian scheme are constructible.** Let `X` be a
scheme whose underlying space is noetherian and `Λ` a noetherian ring. If `ι : F ⟶ G` is a
monomorphism of étale sheaves of `Λ`-modules on `X` and `G` is constructible, then so is `F`.
(blueprint: `lem-weil-pbc-constructible-subobjects-noetherian`) -/
@[stacks 09BH]
theorem IsConstructibleSheaf.of_mono [IsNoetherianRing Λ] [TopologicalSpace.NoetherianSpace X]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ι : F ⟶ G) [Mono ι]
    [IsConstructibleSheaf G] : IsConstructibleSheaf F :=
  sorry

end AlgebraicGeometry.Scheme
